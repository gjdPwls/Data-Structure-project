/*
 * fraud_search.cpp
 *
 * 자료구조 기반 사기 데이터 탐지 시스템
 *
 * [사용자 모드]
 * - 계좌번호 / 전화번호 / 이메일 조회 (교차 참조 연쇄 경고 포함)
 * - 보이스피싱 의심 텍스트 분석 및 교차 검증 (의료/병원 등 11개 카테고리 적용)
 * - 미등록 시 신규 등록 제안
 *
 * [관리자 모드] - 비밀번호: 0000 (해시 기반 위변조 탐지 보안 로그인 적용)
 * - 데이터 추가 (중복 방지 + Trie & CSV 동시 갱신)
 * - 데이터 삭제 (재귀 물리 삭제 + 컬럼 기반 CSV 행 제거)
 * - 전위순회 전체 조회
 * - [NEW] 삭제한 데이터 복구 기능 (Undo)
 *
 * [보안 기능]
 * - [NEW] XOR 메모리 덤프 방어 (메모리 난독화)
 * - [NEW] 허니팟(Honeypot) 미끼 스캐닝 방어
 */

#define _CRT_SECURE_NO_WARNINGS

#ifdef _MSC_VER
#pragma execution_character_set("utf-8")
#endif

#include <iostream>
#include <string>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <ctime>
#include <vector>
#include <sstream>
#include <regex>
#include <functional>
#include <map>
#include <algorithm>
#include <set>

using namespace std;

#define MAX_LINE    1024
#define MAX_TOKEN    256
#define MAX_COL       20

#define COL_NAME         0
#define COL_REPORT_DATE  1
#define COL_REPORT_COUNT 2
#define COL_BANK         3
#define COL_ACCOUNT      4
#define COL_EMAIL        5
#define COL_PHONE        6
#define COL_FRAUD_TYPE   7
#define COL_FRAUD_PLATFORM 8

#define DB_PATH        "fraud_accounts_str.csv"
#define ADMIN_PASSWORD "0000"

// 서버와 클라이언트가 공유하는 비밀 키 (위변조 탐지용)
const string SECRET_KEY = "smu_secure_2026";

// [보안] 메모리 보호용 XOR 난독화 키 및 함수
const string MEMORY_KEY = "smu_memory_protect";

string xorCipher(const string& text) {
    if (text == "-" || text.empty()) return text;
    string result = text;
    for (size_t i = 0; i < text.size(); ++i) {
        result[i] = text[i] ^ MEMORY_KEY[i % MEMORY_KEY.size()];
    }
    return result;
}


// =========================================================
// [개인정보 마스킹 함수]
// - 계좌번호는 사기 조회 목적상 원문 그대로 표시
// - 성함, 전화번호, 이메일은 화면 출력 시에만 마스킹
// - Trie/CSV 저장값과 검색 키는 원본을 유지하므로 기존 검색 로직은 변경 없음
// =========================================================
bool isEmptyOrDash(const string& value) {
    return value.empty() || value == "-";
}

vector<string> splitUtf8Chars(const string& text) {
    vector<string> chars;
    for (size_t i = 0; i < text.size();) {
        unsigned char c = static_cast<unsigned char>(text[i]);
        size_t len = 1;

        if ((c & 0x80) == 0x00) len = 1;
        else if ((c & 0xE0) == 0xC0) len = 2;
        else if ((c & 0xF0) == 0xE0) len = 3;
        else if ((c & 0xF8) == 0xF0) len = 4;

        if (i + len > text.size()) len = 1;
        chars.push_back(text.substr(i, len));
        i += len;
    }
    return chars;
}

string getDigitsOnly(const string& value) {
    string digits;
    for (char ch : value) {
        if (isdigit(static_cast<unsigned char>(ch))) digits += ch;
    }
    return digits;
}

string maskName(const string& name) {
    if (isEmptyOrDash(name)) return "-";

    vector<string> chars = splitUtf8Chars(name);
    if (chars.empty()) return "-";
    if (chars.size() == 1) return chars[0] + "*";
    if (chars.size() == 2) return chars[0] + "*";

    string result = chars.front();
    for (size_t i = 1; i + 1 < chars.size(); ++i) result += "*";
    result += chars.back();
    return result;
}

string maskPhone(const string& phone) {
    if (isEmptyOrDash(phone)) return "-";

    string digits = getDigitsOnly(phone);
    if (digits.empty()) return "-";

    if (digits.size() == 11 && digits.rfind("010", 0) == 0) {
        return digits.substr(0, 3) + "-****-" + digits.substr(7, 4);
    }

    if (digits.size() <= 4) return string(digits.size(), '*');
    return string(digits.size() - 4, '*') + digits.substr(digits.size() - 4);
}

string maskEmail(const string& email) {
    if (isEmptyOrDash(email)) return "-";

    size_t at = email.find('@');
    if (at == string::npos) {
        vector<string> chars = splitUtf8Chars(email);
        if (chars.empty()) return "-";
        return chars.front() + "***";
    }

    string local = email.substr(0, at);
    string domain = email.substr(at);
    if (local.empty()) return "***" + domain;

    vector<string> chars = splitUtf8Chars(local);
    if (chars.empty()) return "***" + domain;
    return chars.front() + "***" + domain;
}

string maskedKeyByType(const string& key, int type) {
    if (type == 2) return maskPhone(key);
    if (type == 3) return maskEmail(key);
    return key; // type == 1, 계좌번호는 원문 표시
}

// 해시 생성 함수
string generateHash(const string& payload, const string& key) {
    hash<string> hasher;
    size_t hashValue = hasher(payload + key);
    return to_string(hashValue);
}

struct TrieNode;

struct ChildNode {
    char       ch;
    TrieNode* child;
    ChildNode* next;
};

struct TrieNode {
    int        isEnd;
    ChildNode* children;

    // [보안] 메모리에는 XOR 암호화된 상태로 저장됩니다.
    string name;
    string report_date;
    string report_count;
    string bank;
    string email;
    string phone;
    string account;
    string fraud_type;
    string fraud_platform;

    // 교차 참조 - 같은 사기꾼의 다른 연락수단 목록 (이 배열 안의 문자열도 암호화 보관)
    vector<string> linkedAccounts;
    vector<string> linkedPhones;
    vector<string> linkedEmails;
};

// 삭제 복구용 벡터(스택 역할)
struct DeletedRecord {
    string key;
    string name, report_date, report_count, bank, email, phone, account, fraud_type, fraud_platform;
    int type; // 1=계좌, 2=전화, 3=이메일
};
vector<DeletedRecord> deleteStack;

// 노드 생성
TrieNode* createTrieNode() {
    TrieNode* node = new TrieNode();
    node->isEnd = 0;
    node->children = nullptr;
    return node;
}

// 자식 탐색
TrieNode* findChild(TrieNode* node, char ch) {
    ChildNode* cur = node->children;
    while (cur) {
        if (cur->ch == ch) return cur->child;
        cur = cur->next;
    }
    return nullptr;
}

// 자식 추가
TrieNode* addChild(TrieNode* node, char ch) {
    TrieNode* child = createTrieNode();
    ChildNode* newChild = new ChildNode();
    newChild->ch = ch;
    newChild->child = child;
    newChild->next = node->children;
    node->children = newChild;
    return child;
}

// 삽입 (메모리 덤프 방어 적용)
void insertTrie(TrieNode* root, const string& key,
    const string& name, const string& rd, const string& rc,
    const string& bank, const string& email,
    const string& phone, const string& account,
    const string& fraud_type, const string& fraud_platform,
    const vector<string>& linkedAccounts = {},
    const vector<string>& linkedPhones = {},
    const vector<string>& linkedEmails = {})
{
    TrieNode* cur = root;
    for (char ch : key) {
        TrieNode* next = findChild(cur, ch);
        if (!next) next = addChild(cur, ch);
        cur = next;
    }
    cur->isEnd = 1;

    // 평문이 메모리에 남지 않도록 모두 난독화(XOR) 처리
    cur->name = xorCipher(name);
    cur->report_date = xorCipher(rd);
    cur->report_count = xorCipher(rc);
    cur->bank = xorCipher(bank);
    cur->email = xorCipher(email);
    cur->phone = xorCipher(phone);
    cur->account = xorCipher(account);
    cur->fraud_type = xorCipher(fraud_type);
    cur->fraud_platform = xorCipher(fraud_platform);

    cur->linkedAccounts.clear();
    for (const string& a : linkedAccounts) cur->linkedAccounts.push_back(xorCipher(a));
    cur->linkedPhones.clear();
    for (const string& p : linkedPhones) cur->linkedPhones.push_back(xorCipher(p));
    cur->linkedEmails.clear();
    for (const string& e : linkedEmails) cur->linkedEmails.push_back(xorCipher(e));
}

// 탐색
TrieNode* searchTrie(TrieNode* root, const string& key) {
    TrieNode* cur = root;
    for (char ch : key) {
        TrieNode* next = findChild(cur, ch);
        if (!next) return nullptr;
        cur = next;
    }
    return cur->isEnd ? cur : nullptr;
}

// 삭제를 위한 자식 확인
bool hasChildren(TrieNode* node) {
    return node->children != nullptr;
}

bool deleteTrieHelper(TrieNode* cur, const string& key, size_t depth) {
    if (!cur) return false;

    if (depth == key.size()) {
        if (cur->isEnd) {
            cur->isEnd = 0;
            return !hasChildren(cur);
        }
        return false;
    }

    char ch = key[depth];
    ChildNode* prev = nullptr;
    ChildNode* currChild = cur->children;
    TrieNode* nextNode = nullptr;

    while (currChild) {
        if (currChild->ch == ch) { nextNode = currChild->child; break; }
        prev = currChild;
        currChild = currChild->next;
    }
    if (!nextNode) return false;

    bool shouldDelete = deleteTrieHelper(nextNode, key, depth + 1);

    if (shouldDelete) {
        if (!prev) cur->children = currChild->next;
        else       prev->next = currChild->next;

        delete nextNode;
        delete currChild;

        return !cur->isEnd && !hasChildren(cur);
    }
    return false;
}

void deleteTrie(TrieNode* root, const string& key) {
    if (key.empty()) return;
    deleteTrieHelper(root, key, 0);
}

// 전위순회 출력 (복호화 적용)
void printAllTrie(TrieNode* node, const string& prefix, int type) {
    if (!node) return;

    if (node->isEnd) {
        cout << "  ▶ [" << maskedKeyByType(prefix, type) << "]"
            << "  성함: " << (node->name.empty() ? "-" : maskName(xorCipher(node->name)))
            << "  |  은행: " << (node->bank.empty() ? "-" : xorCipher(node->bank))
            << "  |  신고횟수: " << (node->report_count.empty() ? "-" : xorCipher(node->report_count))
            << "  |  최근신고일: " << (node->report_date.empty() ? "-" : xorCipher(node->report_date))
            << "  |  사기유형: " << (node->fraud_type.empty() ? "-" : xorCipher(node->fraud_type))
            << "  |  플랫폼: " << (node->fraud_platform.empty() ? "-" : xorCipher(node->fraud_platform))
            << "\n";
    }

    ChildNode* cur = node->children;
    while (cur) {
        printAllTrie(cur->child, prefix + cur->ch, type);
        cur = cur->next;
    }
}


// 입력 정규화 / 유형 판별
void normalizeNumber(char* dest, const char* src) {
    int j = 0;
    for (int i = 0; src[i]; i++)
        if (isdigit((unsigned char)src[i]))
            dest[j++] = src[i];
    dest[j] = '\0';
}

void normalizeEmail(char* dest, const char* src) {
    int j = 0;
    for (int i = 0; src[i]; i++)
        if (src[i] != ' ' && src[i] != '\n' && src[i] != '\r')
            dest[j++] = (char)tolower((unsigned char)src[i]);
    dest[j] = '\0';
}

void trimRight(char* s) {
    int len = (int)strlen(s);
    while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r' || s[len - 1] == ' '))
        s[--len] = '\0';
}

int isPhoneNumber(const char* str) {
    char num[MAX_TOKEN];
    normalizeNumber(num, str);
    return (int)strlen(num) == 11 && strncmp(num, "010", 3) == 0;
}

int isEmail(const char* str) {
    return strchr(str, '@') != nullptr;
}

int isAccountNumber(const char* str) {
    char num[MAX_TOKEN];
    normalizeNumber(num, str);
    int len = (int)strlen(num);
    return (len >= 10 && len <= 14);
}

const char* identifyBank(const char* acc) {
    char num[MAX_TOKEN];
    normalizeNumber(num, acc);
    int len = (int)strlen(num);
    if (len == 12 && (strncmp(num, "110", 3) == 0 || strncmp(num, "100", 3) == 0)) return "신한은행";
    if (len == 13 && strncmp(num, "1002", 4) == 0)                          return "우리은행";
    if (len == 14 && (strncmp(num, "101", 3) == 0 || strncmp(num, "102", 3) == 0 ||
        strncmp(num, "620", 3) == 0))                          return "하나은행";
    if (len == 13 && (strncmp(num, "301", 3) == 0 || strncmp(num, "302", 3) == 0 ||
        strncmp(num, "351", 3) == 0 || strncmp(num, "352", 3) == 0)) return "NH농협은행";
    if (len == 14 && strncmp(num, "022", 3) == 0)                           return "KDB산업은행";
    if (len >= 10 && len <= 14)                                            return "국민/기업은행";
    return "미분류";
}

void getCurrentDate(char* buf) {
    time_t now = time(nullptr);
    struct tm t;
#ifdef _WIN32
    localtime_s(&t, &now);
#else
    localtime_r(&now, &t);
#endif
    strftime(buf, 32, "%Y-%m-%d", &t);
}

// CSV 파싱
int parseCSVLine(char* line, char* columns[], int maxCol) {
    int col = 0, inQuote = 0;
    char* start = line;
    for (char* p = line; *p; p++) {
        if (*p == '"') { inQuote = !inQuote; }
        else if (*p == ',' && !inQuote) {
            *p = '\0';
            columns[col++] = start;
            start = p + 1;
            if (col >= maxCol) break;
        }
    }
    columns[col++] = start;
    return col;
}

// CSV 로드 (2패스 교차 참조 지원)
void loadCSV(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot,
    const char* filename)
{
    FILE* fp = fopen(filename, "r");
    if (!fp) {
        cout << "[오류] CSV 파일을 열 수 없습니다: " << filename << "\n"
            << "       빈 DB로 시작합니다.\n";
        return;
    }

    struct RawRecord {
        string name, rd, rc, bank, acc, email, phone, f_type, f_platform;
    };
    vector<RawRecord> allRecords;

    char line[MAX_LINE];
    fgets(line, sizeof(line), fp); // 헤더 스킵

    while (fgets(line, sizeof(line), fp)) {
        if (line[0] == '\n' || line[0] == '\r') continue;

        char lineCopy[MAX_LINE];
        strcpy(lineCopy, line);
        char* cols[MAX_COL];
        int n = parseCSVLine(lineCopy, cols, MAX_COL);
        if (n <= COL_PHONE) continue;

        RawRecord r;
        char tmp[MAX_TOKEN];
        memset(tmp, 0, sizeof(tmp));

        if (n > COL_NAME) { strncpy(tmp, cols[COL_NAME], MAX_TOKEN - 1); trimRight(tmp); r.name = tmp; }
        if (n > COL_REPORT_DATE) {
            strncpy(tmp, cols[COL_REPORT_DATE], MAX_TOKEN - 1); trimRight(tmp);
            char* pipe = strrchr(tmp, '|'); if (pipe) memmove(tmp, pipe + 1, strlen(pipe));
            r.rd = tmp;
        }
        if (n > COL_REPORT_COUNT) { strncpy(tmp, cols[COL_REPORT_COUNT], MAX_TOKEN - 1); trimRight(tmp); r.rc = tmp; }
        if (n > COL_BANK) { strncpy(tmp, cols[COL_BANK], MAX_TOKEN - 1); trimRight(tmp); r.bank = tmp; }
        if (n > COL_FRAUD_TYPE) { strncpy(tmp, cols[COL_FRAUD_TYPE], MAX_TOKEN - 1); trimRight(tmp); r.f_type = tmp; }
        if (n > COL_FRAUD_PLATFORM) { strncpy(tmp, cols[COL_FRAUD_PLATFORM], MAX_TOKEN - 1); trimRight(tmp); r.f_platform = tmp; }

        if (n > COL_ACCOUNT) {
            char raw[MAX_TOKEN]; strncpy(raw, cols[COL_ACCOUNT], MAX_TOKEN - 1); trimRight(raw);
            int j = 0;
            for (int i = 0; raw[i]; i++) if (raw[i] != '"' && raw[i] != ' ') tmp[j++] = raw[i];
            tmp[j] = '\0';
            normalizeNumber(tmp, tmp);
            r.acc = tmp;
        }
        if (n > COL_PHONE) { char p[MAX_TOKEN]; normalizeNumber(p, cols[COL_PHONE]); trimRight(p); r.phone = p; }
        if (n > COL_EMAIL) { char e[MAX_TOKEN]; normalizeEmail(e, cols[COL_EMAIL]); r.email = e; }

        allRecords.push_back(r);
    }
    fclose(fp);

    map<string, vector<int>> nameGroups;
    for (int i = 0; i < (int)allRecords.size(); i++)
        nameGroups[allRecords[i].name].push_back(i);

    int count = 0;
    for (auto& group : nameGroups) {
        vector<string> accounts, phones, emails;
        for (int idx : group.second) {
            if (!allRecords[idx].acc.empty())   accounts.push_back(allRecords[idx].acc);
            if (!allRecords[idx].phone.empty()) phones.push_back(allRecords[idx].phone);
            if (!allRecords[idx].email.empty()) emails.push_back(allRecords[idx].email);
        }
        for (int idx : group.second) {
            auto& r = allRecords[idx];
            vector<string> oAccs = accounts, oPhones = phones, oEmails = emails;
            oAccs.erase(remove(oAccs.begin(), oAccs.end(), r.acc), oAccs.end());
            oPhones.erase(remove(oPhones.begin(), oPhones.end(), r.phone), oPhones.end());
            oEmails.erase(remove(oEmails.begin(), oEmails.end(), r.email), oEmails.end());

            if (!r.acc.empty())
                insertTrie(accountRoot, r.acc, r.name, r.rd, r.rc, r.bank,
                    "-", "-", r.acc, r.f_type, r.f_platform, oAccs, oPhones, oEmails);
            if (!r.phone.empty())
                insertTrie(phoneRoot, r.phone, r.name, r.rd, r.rc, r.bank,
                    r.email.empty() ? "-" : r.email, r.phone, r.acc,
                    r.f_type, r.f_platform, oAccs, oPhones, oEmails);
            if (!r.email.empty())
                insertTrie(emailRoot, r.email, r.name, r.rd, r.rc, r.bank,
                    r.email, r.phone.empty() ? "-" : r.phone, r.acc,
                    r.f_type, r.f_platform, oAccs, oPhones, oEmails);
            count++;
        }
    }
    cout << "[시스템] 초기 데이터 연동 완료. (총 " << count << "건)\n";
}

void deleteFromCSV(const string& key, int colIndex) {
    FILE* fp = fopen(DB_PATH, "r");
    FILE* temp = fopen("temp.csv", "w");

    if (!fp || !temp) {
        if (fp)   fclose(fp);
        if (temp) fclose(temp);
        cout << "[오류] 파일 입출력 권한 획득 실패\n";
        return;
    }

    char line[MAX_LINE];
    if (fgets(line, sizeof(line), fp))
        fprintf(temp, "%s", line);

    int removed = 0;
    while (fgets(line, sizeof(line), fp)) {
        char lineCopy[MAX_LINE];
        strcpy(lineCopy, line);

        char* cols[MAX_COL];
        int n = parseCSVLine(lineCopy, cols, MAX_COL);
        bool isTarget = false;

        if (colIndex == COL_EMAIL && n > COL_EMAIL) {
            char norm[MAX_TOKEN]; normalizeEmail(norm, cols[COL_EMAIL]);
            if (key == norm) isTarget = true;
        }
        else if (colIndex == COL_PHONE && n > COL_PHONE) {
            char norm[MAX_TOKEN]; normalizeNumber(norm, cols[COL_PHONE]);
            if (key == norm) isTarget = true;
        }
        else if (colIndex == COL_ACCOUNT && n > COL_ACCOUNT) {
            char raw[MAX_TOKEN]; strncpy(raw, cols[COL_ACCOUNT], MAX_TOKEN - 1); trimRight(raw);
            char acc[MAX_TOKEN]; int j = 0;
            for (int i = 0; raw[i]; i++) if (raw[i] != '"' && raw[i] != ' ') acc[j++] = raw[i];
            acc[j] = '\0';
            normalizeNumber(acc, acc);
            if (key == acc) isTarget = true;
        }

        if (!isTarget) fprintf(temp, "%s", line);
        else           removed++;
    }

    fclose(fp);
    fclose(temp);
    remove(DB_PATH);
    rename("temp.csv", DB_PATH);
    cout << "  [파일 갱신] CSV에서 " << removed << "건 삭제 완료\n";
}

// 결과 출력 (복호화 연산 포함)
void printResult(TrieNode* res, const char* inputKey, int type) {
    cout << "\n==========================================\n"
        << "  !!! [사기 의심 기록 탐지 성공] !!!      \n"
        << "==========================================\n"
        << "  성함       : " << (!res->name.empty() ? maskName(xorCipher(res->name)) : "-") << "\n"
        << "  은행       : " << (!res->bank.empty() ? xorCipher(res->bank) : "-") << "\n"
        << "  계좌번호   : " << (!res->account.empty() ? xorCipher(res->account) : (type == 1 ? inputKey : "-")) << "\n"
        << "  전화번호   : " << (!res->phone.empty() ? maskPhone(xorCipher(res->phone)) : (type == 2 ? maskPhone(inputKey) : "-")) << "\n"
        << "  이메일     : " << (!res->email.empty() ? maskEmail(xorCipher(res->email)) : (type == 3 ? maskEmail(inputKey) : "-")) << "\n"
        << "  신고 날짜  : " << (!res->report_date.empty() ? xorCipher(res->report_date) : "-") << "\n"
        << "  신고 횟수  : " << (!res->report_count.empty() ? xorCipher(res->report_count) : "-") << "\n"
        << "  사기 유형  : " << (!res->fraud_type.empty() ? xorCipher(res->fraud_type) : "-") << "\n"
        << "  사기 플랫폼: " << (!res->fraud_platform.empty() ? xorCipher(res->fraud_platform) : "-") << "\n"
        << "==========================================\n";
}

void registerNewUser(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot,
    const char* filename, int type, const char* key)
{
    cout << "\n[신규 등록 안내]\n  피신고자 성함 (모를 경우 Enter): ";
    char name[MAX_TOKEN] = "-";
    char input[MAX_TOKEN];
    if (fgets(input, sizeof(input), stdin)) {
        trimRight(input);
        if (strlen(input) > 0) strncpy(name, input, MAX_TOKEN - 1);
    }

    char rd[32]; getCurrentDate(rd);
    char bank[MAX_TOKEN] = "-", acc[MAX_TOKEN] = "-", email[MAX_TOKEN] = "-", phone[MAX_TOKEN] = "-";

    cout << "  사기 유형 (예: 보이스피싱, 중고거래 사기 등) (모를 경우 Enter): ";
    char f_type[MAX_TOKEN] = "-";
    if (fgets(input, sizeof(input), stdin)) {
        trimRight(input);
        if (strlen(input) > 0) strncpy(f_type, input, MAX_TOKEN - 1);
    }

    cout << "  사기 플랫폼 (예: 당근마켓, 카카오톡 등) (선택사항, 안 쓰려면 Enter): ";
    char f_platform[MAX_TOKEN] = "-";
    if (fgets(input, sizeof(input), stdin)) {
        trimRight(input);
        if (strlen(input) > 0) strncpy(f_platform, input, MAX_TOKEN - 1);
    }

    if (type == 1) {
        strncpy(acc, key, MAX_TOKEN - 1);
        strncpy(bank, identifyBank(key), MAX_TOKEN - 1);
        insertTrie(accountRoot, key, name, rd, "1", bank, "-", "-", acc, f_type, f_platform);
    }
    else if (type == 2) {
        strncpy(phone, key, MAX_TOKEN - 1);
        insertTrie(phoneRoot, key, name, rd, "1", "-", "-", phone, "-", f_type, f_platform);
    }
    else {
        strncpy(email, key, MAX_TOKEN - 1);
        insertTrie(emailRoot, key, name, rd, "1", "-", email, "-", "-", f_type, f_platform);
    }

    FILE* fp = fopen(filename, "a");
    if (fp) {
        fprintf(fp, "%s,%s,1,%s,\"\"\"%s\"\"\",%s,%s,%s,%s\n", name, rd, bank, acc, email, phone, f_type, f_platform);
        fclose(fp);
        cout << "\n[완료] " << rd << " 날짜로 Trie 및 CSV에 등록되었습니다.\n";
    }
    else cout << "[오류] CSV 파일 저장에 실패했습니다.\n";
}


// 보이스피싱 텍스트 분석 및 Trie DB 교차 검증 함수
void analyzeVoicePhishing(TrieNode* accountRoot, TrieNode* phoneRoot) {
    std::vector<string> warningKeywords = {
        "응급실", "수술비", "병원비", "입원", "교통사고", "건강검진",
        "국민건강보험공단", "건강보험", "진단서", "처방전", "보험금청구",
        "실비청구", "암진단", "건강검진결과", "안전계좌", "가상계좌", "보안계좌",
        "국가안전보안계좌", "대포통장", "통장대여", "자금세탁", "예치금",
        "동결처리", "지급정지", "보호조치", "비밀번호", "보안카드", "일회성비밀번호",
        "OTP", "이체한도", "검찰", "경찰", "금융감독원", "금감원", "수사관", "검사",
        "사이버수사대", "서울중앙지검", "출석요구서", "고소장", "사건번호",
        "영장", "구속", "압수수색", "형사고발", "불법도박", "연루", "자금추적",
        "원격제어", "apk", "설치", "팀뷰어", "애니데스크", "다운로드",
        "악성앱", "보안앱", "링크", "url", "클릭", "인증번호", "신분증사본",
        "저금리", "대환대출", "신용등급", "정부지원", "특례", "보증금",
        "수수료", "선입금", "신용불량", "마이너스통장", "대출승인", "상환",
        "문화상품권", "구글기프트", "기프트카드", "핀번호", "소액결제",
        "대리결제", "위약금", "결제승인", "해외결제", "미납금", "다날",
        "액정", "폰고장", "수리비", "편의점", "기기변경", "엄마", "아빠", "자녀",
        "리딩방", "코인", "가상화폐", "급등주", "고수익", "원금보장", "투자금",
        "수익금", "바람잡이", "가상자산", "상장폐지", "프라이빗세일",
        "택배", "반송", "주소불일치", "통관", "부고", "모바일청첩장", "돌잔치",
        "과태료", "교통위반", "쓰레기투기", "국세청",
        "재택근무", "고수익알바", "쇼핑몰리뷰", "단기알바", "타이핑", "합격",
        "채용", "통장제출", "체크카드제출", "물품대금",
        "해외로그인", "비밀번호변경", "비정상접근", "아이피", "계정잠금",
        "애플", "구글", "본인인증", "결제완료", "비밀번호오류"
    };

    cout << "\n==========================================\n"
        << "  [AI 텍스트 분석 및 DB 교차 검증기]\n"
        << "==========================================\n"
        << "받으신 문자 메시지나 통화 내용을 입력해 주세요.\n"
        << "(입력을 마치려면 '엔터'를 누르세요)\n입력: ";

    char input[MAX_LINE];
    if (!fgets(input, sizeof(input), stdin)) return;
    trimRight(input);

    string text = input;
    vector<string> detectedWords;
    int dangerScore = 0;

    for (const string& keyword : warningKeywords) {
        if (text.find(keyword) != string::npos) {
            detectedWords.push_back(keyword);
            dangerScore += 20;
        }
    }

    cout << "\n분석 중... [■■■■■■■■■■]\n------------------------------------------\n[식별 정보 자동 추출 및 Trie 검증 결과]\n";
    bool foundInDB = false;

    std::regex phoneRegex("010[- .]?\\d{4}[- .]?\\d{4}");
    auto phone_begin = std::sregex_iterator(text.begin(), text.end(), phoneRegex);
    auto phone_end = std::sregex_iterator();

    for (std::sregex_iterator i = phone_begin; i != phone_end; ++i) {
        string match = i->str();
        char normPhone[MAX_TOKEN]; normalizeNumber(normPhone, match.c_str());

        cout << "  📞 텍스트 내 전화번호 발견 : " << maskPhone(match) << "\n";
        TrieNode* res = searchTrie(phoneRoot, normPhone);
        if (res) {
            // [보안] 허니팟 트랩 체크
            if (xorCipher(res->name) == "HONEYPOT_TRAP") {
                cout << "\n==================================================\n";
                cout << " [🚨 치명적 보안 위협 감지 🚨] 허니팟 트랩 발동!\n";
                cout << " - 비정상적인 미끼 데이터 스캐닝 시도가 감지되었습니다.\n";
                cout << " - 시스템을 강제 잠금 처리합니다.\n";
                cout << "==================================================\n";
                exit(1);
            }
            cout << "     [🚨 사기 DB 일치!] 등록명: " << maskName(xorCipher(res->name)) << " / 신고횟수: " << xorCipher(res->report_count) << "회\n";
            dangerScore += 100;
            foundInDB = true;
        }
        else cout << "     [✓ DB 미등록 번호]\n";
    }

    std::regex accountRegex("\\d{3,4}[- .]?\\d{3,4}[- .]?\\d{4,6}");
    auto acc_begin = std::sregex_iterator(text.begin(), text.end(), accountRegex);
    auto acc_end = std::sregex_iterator();

    for (std::sregex_iterator i = acc_begin; i != acc_end; ++i) {
        string match = i->str();
        char normAcc[MAX_TOKEN]; normalizeNumber(normAcc, match.c_str());

        if (strlen(normAcc) >= 10 && strlen(normAcc) <= 14 && strncmp(normAcc, "010", 3) != 0) {
            cout << "  🏦 텍스트 내 계좌번호 발견 : " << match << "\n";
            TrieNode* res = searchTrie(accountRoot, normAcc);
            if (res) {
                // [보안] 허니팟 트랩 체크
                if (xorCipher(res->name) == "HONEYPOT_TRAP") {
                    cout << "\n==================================================\n";
                    cout << " [🚨 치명적 보안 위협 감지 🚨] 허니팟 트랩 발동!\n";
                    cout << " - 비정상적인 미끼 데이터 스캐닝 시도가 감지되었습니다.\n";
                    cout << " - 시스템을 강제 잠금 처리합니다.\n";
                    cout << "==================================================\n";
                    exit(1);
                }
                cout << "     [🚨 사기 DB 일치!] 은행: " << xorCipher(res->bank) << " / 등록명: " << maskName(xorCipher(res->name)) << "\n";
                dangerScore += 100;
                foundInDB = true;
            }
            else cout << "     [✓ DB 미등록 계좌]\n";
        }
    }

    if (dangerScore > 100) dangerScore = 100;
    cout << "\n==========================================\n";
    if (dangerScore >= 60 || foundInDB) {
        cout << " [🚨 심각 🚨] 사기 및 보이스피싱 확률: " << dangerScore << "%\n";
        if (foundInDB) cout << " (사유: 사기 DB에 등록된 식별 정보가 텍스트에 포함되어 있습니다!)\n";
        cout << " 절대 송금하거나 지시를 따르지 마십시오!\n";
    }
    else if (dangerScore > 0) cout << " [⚠️ 주의 ⚠️] 보이스피싱 확률: " << dangerScore << "%\n 사기 목적의 접근일 가능성이 높습니다.\n";
    else cout << " [✓ 양호] 위험 키워드 및 사기 DB 일치 항목이 없습니다.\n";

    if (!detectedWords.empty()) {
        cout << "------------------------------------------\n * 탐지된 위험 문맥: ";
        for (const string& w : detectedWords) cout << "[" << w << "] ";
        cout << "\n";
    }
    cout << "==========================================\n";
}


// 유형 및 플랫폼 기반 다중 검색
void searchByCategoryHelper(TrieNode* node, const string& keyword, bool isPlatform, set<string>& seen, vector<TrieNode*>& results) {
    if (!node) return;

    if (node->isEnd) {
        string target = isPlatform ? xorCipher(node->fraud_platform) : xorCipher(node->fraud_type);
        if (target != "-" && target.find(keyword) != string::npos) {
            // 중복 방지를 위해 (이름 + 계좌번호 + 번호) 조합 키 사용
            string uniqKey = xorCipher(node->name) + "_" + xorCipher(node->account) + "_" + xorCipher(node->phone);
            if (seen.find(uniqKey) == seen.end()) {
                seen.insert(uniqKey);
                results.push_back(node);
            }
        }
    }

    ChildNode* cur = node->children;
    while (cur) {
        searchByCategoryHelper(cur->child, keyword, isPlatform, seen, results);
        cur = cur->next;
    }
}

void searchByCategory(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot, const string& keyword, bool isPlatform) {
    set<string> seen;
    vector<TrieNode*> results;

    searchByCategoryHelper(accountRoot, keyword, isPlatform, seen, results);
    searchByCategoryHelper(phoneRoot, keyword, isPlatform, seen, results);
    searchByCategoryHelper(emailRoot, keyword, isPlatform, seen, results);

    cout << "\n==========================================\n";
    cout << "  [ " << keyword << " ] 관련 검색 결과 (" << results.size() << "건)\n";
    cout << "==========================================\n";
    
    if (results.empty()) {
        cout << "  해당 조건에 일치하는 데이터가 없습니다.\n";
        cout << "==========================================\n";
        return;
    }

    for (size_t i = 0; i < results.size(); ++i) {
        TrieNode* res = results[i];
        cout << " [" << i + 1 << "] 성함: " << (!res->name.empty() ? maskName(xorCipher(res->name)) : "-")
             << " | 은행: " << (!res->bank.empty() ? xorCipher(res->bank) : "-")
             << " | 계좌: " << (!res->account.empty() ? xorCipher(res->account) : "-")
             << " | 번호: " << (!res->phone.empty() ? maskPhone(xorCipher(res->phone)) : "-")
             << " | 이메일: " << (!res->email.empty() ? maskEmail(xorCipher(res->email)) : "-") << "\n"
             << "     -> 사기유형: " << (!res->fraud_type.empty() ? xorCipher(res->fraud_type) : "-")
             << " / 플랫폼: " << (!res->fraud_platform.empty() ? xorCipher(res->fraud_platform) : "-") << "\n"
             << "     -> 최근 신고일: " << (!res->report_date.empty() ? xorCipher(res->report_date) : "-") 
             << " (" << (!res->report_count.empty() ? xorCipher(res->report_count) : "-") << "회 신고)\n";
        cout << "------------------------------------------\n";
    }
}


// 사용자 모드 메인 함수
void runSearch(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot,
    const char* filename)
{
    cout << "\n------------------------------------------\n"
        << "[사용자 모드 - 의심 정보 조회]\n"
        << "  1. 계좌번호 조회\n  2. 전화번호 조회\n  3. 이메일 조회\n  4. 보이스피싱 의심 텍스트 분석 및 교차 검증\n"
        << "  5. 사기 유형으로 조회\n  6. 사기 플랫폼으로 조회\n선택: ";

    int menu;
    if (!(cin >> menu)) { cin.clear(); cin.ignore(1000, '\n'); return; }
    cin.ignore(1000, '\n');

    if (menu < 1 || menu > 6) { cout << "[경고] 잘못된 카테고리입니다.\n"; return; }
    if (menu == 4) { analyzeVoicePhishing(accountRoot, phoneRoot); return; }

    if (menu == 5 || menu == 6) {
        cout << (menu == 5 ? "검색할 사기 유형 입력 (예: 보이스피싱): " : "검색할 플랫폼 입력 (예: 당근마켓): ");
        char keywordRaw[MAX_LINE];
        if (!fgets(keywordRaw, sizeof(keywordRaw), stdin)) return;
        trimRight(keywordRaw);
        if (strlen(keywordRaw) == 0) return;
        searchByCategory(accountRoot, phoneRoot, emailRoot, keywordRaw, menu == 6);
        return;
    }

    char raw[MAX_TOKEN], key[MAX_TOKEN];
    if (menu == 1) cout << "조회할 계좌번호 입력: ";
    else if (menu == 2) cout << "조회할 전화번호 입력 (010...): ";
    else                cout << "조회할 이메일 입력: ";

    if (!fgets(raw, sizeof(raw), stdin)) return;
    trimRight(raw);

    TrieNode* res = nullptr;
    if (menu == 1) {
        normalizeNumber(key, raw);
        if (!isAccountNumber(raw)) { cout << "[안내] 계좌번호 형식이 아닙니다. (10~14자리)\n"; return; }
        res = searchTrie(accountRoot, key);
    }
    else if (menu == 2) {
        normalizeNumber(key, raw);
        if (!isPhoneNumber(raw)) { cout << "[안내] 올바른 전화번호 형식이 아닙니다.\n"; return; }
        res = searchTrie(phoneRoot, key);
    }
    else {
        normalizeEmail(key, raw);
        if (!isEmail(raw)) { cout << "[안내] 올바른 이메일 형식이 아닙니다.\n"; return; }
        res = searchTrie(emailRoot, key);
    }

    if (res) {
        // [보안] 허니팟 트랩 체크
        if (xorCipher(res->name) == "HONEYPOT_TRAP") {
            cout << "\n==================================================\n";
            cout << " [🚨 치명적 보안 위협 감지 🚨] 허니팟 트랩 발동!\n";
            cout << " - 비정상적인 미끼 데이터 스캐닝 시도가 감지되었습니다.\n";
            cout << " - 침해 사고 대응 지침에 따라 시스템을 강제 잠금 처리합니다.\n";
            cout << "==================================================\n";
            exit(1);
        }

        printResult(res, key, menu);

        // 연관 정보 복호화 후 출력
        if (!res->linkedAccounts.empty() || !res->linkedPhones.empty() || !res->linkedEmails.empty()) {
            cout << "------------------------------------------\n";
            cout << "  [!] 동일 인물의 다른 신고 이력 발견\n";
            cout << "------------------------------------------\n";
            for (auto& a : res->linkedAccounts) cout << "  연관 계좌  : " << xorCipher(a) << "\n";
            for (auto& p : res->linkedPhones)   cout << "  연관 전화  : " << maskPhone(xorCipher(p)) << "\n";
            for (auto& e : res->linkedEmails)   cout << "  연관 이메일: " << maskEmail(xorCipher(e)) << "\n";
            cout << "------------------------------------------\n";
        }
    }
    else {
        cout << "\n[✓ 안심 결과] 해당 정보는 현재 사기 등록 데이터가 존재하지 않습니다.\n사기 의심 정보로 신규 등록하시겠습니까? (y/n): ";
        char c;
        if (!(cin >> c)) { cin.clear(); cin.ignore(1000, '\n'); return; }
        cin.ignore(1000, '\n');
        if (c == 'y' || c == 'Y') registerNewUser(accountRoot, phoneRoot, emailRoot, filename, menu, key);
    }
}


// 보안 관리자 로그인
bool adminLogin() {
    cout << "\n[보안 관리자 인증]\n  비밀번호 입력: ";
    char pw[MAX_TOKEN];
    if (fgets(pw, sizeof(pw), stdin)) {
        trimRight(pw);
        string clientPayload = pw;
        string clientHash = generateHash(clientPayload, SECRET_KEY);

        if (clientPayload == "hack") {
            cout << "  [!] 네트워크에서 데이터를 가로채 변조를 시도합니다...\n";
            clientPayload = ADMIN_PASSWORD;
        }

        string serverHash = generateHash(clientPayload, SECRET_KEY);
        if (serverHash != clientHash) {
            cout << "\n [🚨 보안 경고 🚨] 데이터 위변조(Tampering) 감지!\n - 시스템 보호를 위해 연결을 즉시 차단합니다.\n";
            return false;
        }

        if (clientPayload == ADMIN_PASSWORD) {
            cout << "  [인증 성공] 패킷 무결성 검증 완료. 관리자 모드로 진입합니다.\n";
            return true;
        }
    }
    cout << "  [인증 실패] 비밀번호가 틀렸습니다.\n";
    return false;
}

void registerNew(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot,
    const char* filename)
{
    cout << "\n[관리자 - 데이터 등록]\n  1. 계좌번호 추가  2. 전화번호 추가  3. 이메일 추가\n  선택: ";
    int type;
    if (!(cin >> type)) { cin.clear(); cin.ignore(1000, '\n'); return; }
    cin.ignore(1000, '\n');

    char rd[32]; getCurrentDate(rd);
    char name[MAX_TOKEN] = "-", rc_str[MAX_TOKEN] = "1", bank[MAX_TOKEN] = "-";
    char acc[MAX_TOKEN] = "-", email[MAX_TOKEN] = "-", phone[MAX_TOKEN] = "-";
    char raw[MAX_TOKEN];

    cout << "  피신고자 성함 (공백 시 Enter): ";
    if (fgets(name, sizeof(name), stdin)) trimRight(name);
    if (strlen(name) == 0) strncpy(name, "-", MAX_TOKEN - 1);

    cout << "  신고 횟수 (기본 1): ";
    if (fgets(rc_str, sizeof(rc_str), stdin)) trimRight(rc_str);
    if (strlen(rc_str) == 0) strncpy(rc_str, "1", MAX_TOKEN - 1);

    cout << "  신고 날짜 (Enter=오늘 " << rd << "): ";
    char dateInput[MAX_TOKEN];
    if (fgets(dateInput, sizeof(dateInput), stdin)) {
        trimRight(dateInput);
        if (strlen(dateInput) > 0) strncpy(rd, dateInput, 31);
    }

    cout << "  사기 유형 (예: 보이스피싱, 중고거래 사기 등) (모를 경우 Enter): ";
    char f_type[MAX_TOKEN] = "-";
    if (fgets(raw, sizeof(raw), stdin)) {
        trimRight(raw);
        if (strlen(raw) > 0) strncpy(f_type, raw, MAX_TOKEN - 1);
    }

    cout << "  사기 플랫폼 (예: 당근마켓, 카카오톡 등) (선택사항, 안 쓰려면 Enter): ";
    char f_platform[MAX_TOKEN] = "-";
    if (fgets(raw, sizeof(raw), stdin)) {
        trimRight(raw);
        if (strlen(raw) > 0) strncpy(f_platform, raw, MAX_TOKEN - 1);
    }

    if (type == 1) {
        cout << "  등록 계좌번호 입력: ";
        if (fgets(raw, sizeof(raw), stdin)) trimRight(raw);
        normalizeNumber(acc, raw);
        if (!isAccountNumber(raw)) { cout << "  [오류] 유효하지 않은 계좌번호\n"; return; }
        if (searchTrie(accountRoot, acc)) { cout << "  [거부] 이미 등록된 계좌번호입니다.\n"; return; }
        strncpy(bank, identifyBank(acc), MAX_TOKEN - 1);
        insertTrie(accountRoot, acc, name, rd, rc_str, bank, "-", "-", acc, f_type, f_platform);
    }
    else if (type == 2) {
        cout << "  등록 전화번호 입력: ";
        if (fgets(raw, sizeof(raw), stdin)) trimRight(raw);
        normalizeNumber(phone, raw);
        if (!isPhoneNumber(raw)) { cout << "  [오류] 유효하지 않은 전화번호\n"; return; }
        if (searchTrie(phoneRoot, phone)) { cout << "  [거부] 이미 등록된 전화번호입니다.\n"; return; }
        insertTrie(phoneRoot, phone, name, rd, rc_str, "-", "-", phone, "-", f_type, f_platform);
    }
    else if (type == 3) {
        cout << "  등록 이메일 입력: ";
        if (fgets(raw, sizeof(raw), stdin)) trimRight(raw);
        normalizeEmail(email, raw);
        if (!isEmail(raw)) { cout << "  [오류] 유효하지 않은 이메일\n"; return; }
        if (searchTrie(emailRoot, email)) { cout << "  [거부] 이미 등록된 이메일입니다.\n"; return; }
        insertTrie(emailRoot, email, name, rd, rc_str, "-", email, "-", "-", f_type, f_platform);
    }
    else return;

    FILE* fp = fopen(filename, "a");
    if (fp) {
        fprintf(fp, "%s,%s,%s,%s,\"\"\"%s\"\"\",%s,%s,%s,%s\n", name, rd, rc_str, bank, acc, email, phone, f_type, f_platform);
        fclose(fp);
        cout << "\n[성공] " << rd << " 날짜로 Trie 및 CSV에 등록 완료.\n";
    }
}

// 삭제 시 복구를 위해 스택에 복호화된 평문 상태로 백업
void adminDeleteData(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot) {
    cout << "\n[관리자 - 데이터 삭제]\n  삭제할 키워드 (계좌/전화/이메일) 입력: ";
    string delKey;
    if (!(cin >> delKey)) { cin.clear(); cin.ignore(1000, '\n'); return; }
    cin.ignore(1000, '\n');

    if (isEmail(delKey.c_str())) {
        TrieNode* t = searchTrie(emailRoot, delKey);
        if (!t) { cout << "  [결과] 등록되지 않은 이메일입니다.\n"; return; }
        cout << "  대상: " << maskName(xorCipher(t->name)) << " / " << maskEmail(delKey) << "\n  삭제하시겠습니까? (y/n): ";
        char c; cin >> c; cin.ignore(1000, '\n');
        if (c != 'y' && c != 'Y') { cout << "  삭제 취소\n"; return; }

        // [Undo 연동] 평문 상태로 스택에 백업
        deleteStack.push_back({ delKey, xorCipher(t->name), xorCipher(t->report_date), xorCipher(t->report_count),
                                xorCipher(t->bank), xorCipher(t->email), xorCipher(t->phone), xorCipher(t->account),
                                xorCipher(t->fraud_type), xorCipher(t->fraud_platform), 3 });
        if (deleteStack.size() > 20) deleteStack.erase(deleteStack.begin());
        deleteTrie(emailRoot, delKey);
        deleteFromCSV(delKey, COL_EMAIL);
        cout << "  → 이메일 Trie 메모리 해제 및 CSV 갱신 완료\n  [안내] 복구 메뉴(4번)를 통해 복구 가능\n";
    }
    else if (isPhoneNumber(delKey.c_str())) {
        char norm[MAX_TOKEN]; normalizeNumber(norm, delKey.c_str());
        TrieNode* t = searchTrie(phoneRoot, norm);
        if (!t) { cout << "  [결과] 등록되지 않은 전화번호입니다.\n"; return; }
        cout << "  대상: " << maskName(xorCipher(t->name)) << " / " << maskPhone(norm) << "\n  삭제하시겠습니까? (y/n): ";
        char c; cin >> c; cin.ignore(1000, '\n');
        if (c != 'y' && c != 'Y') { cout << "  삭제 취소\n"; return; }

        deleteStack.push_back({ norm, xorCipher(t->name), xorCipher(t->report_date), xorCipher(t->report_count),
                                xorCipher(t->bank), xorCipher(t->email), xorCipher(t->phone), xorCipher(t->account),
                                xorCipher(t->fraud_type), xorCipher(t->fraud_platform), 2 });
        if (deleteStack.size() > 20) deleteStack.erase(deleteStack.begin());
        deleteTrie(phoneRoot, norm);
        deleteFromCSV(norm, COL_PHONE);
        cout << "  → 전화번호 Trie 메모리 해제 및 CSV 갱신 완료\n  [안내] 복구 메뉴(4번)를 통해 복구 가능\n";
    }
    else if (isAccountNumber(delKey.c_str())) {
        char norm[MAX_TOKEN]; normalizeNumber(norm, delKey.c_str());
        TrieNode* t = searchTrie(accountRoot, norm);
        if (!t) { cout << "  [결과] 등록되지 않은 계좌번호입니다.\n"; return; }
        cout << "  대상: " << maskName(xorCipher(t->name)) << " / " << norm << "\n  삭제하시겠습니까? (y/n): ";
        char c; cin >> c; cin.ignore(1000, '\n');
        if (c != 'y' && c != 'Y') { cout << "  삭제 취소\n"; return; }

        deleteStack.push_back({ norm, xorCipher(t->name), xorCipher(t->report_date), xorCipher(t->report_count),
                                xorCipher(t->bank), xorCipher(t->email), xorCipher(t->phone), xorCipher(t->account),
                                xorCipher(t->fraud_type), xorCipher(t->fraud_platform), 1 });
        if (deleteStack.size() > 20) deleteStack.erase(deleteStack.begin());
        deleteTrie(accountRoot, norm);
        deleteFromCSV(norm, COL_ACCOUNT);
        cout << "  → 계좌 Trie 메모리 해제 및 CSV 갱신 완료\n  [안내] 복구 메뉴(4번)를 통해 복구 가능\n";
    }
    else cout << "  [오류] 인식할 수 없는 형식입니다.\n";
}

// [NEW] 삭제 데이터 복구 (Undo)
void adminUndoDelete(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot,
    const char* filename)
{
    if (deleteStack.empty()) {
        cout << "\n  [안내] 복구할 데이터가 없습니다. (삭제 이력 없음)\n"; return;
    }
    cout << "\n[관리자 - 삭제 복구]\n  최근 삭제 목록:\n";
    for (int i = (int)deleteStack.size() - 1; i >= 0; i--) {
        string t = deleteStack[i].type == 1 ? "계좌" : deleteStack[i].type == 2 ? "전화" : "이메일";
        cout << "  [" << ((int)deleteStack.size() - i) << "] " << t
            << " | " << maskedKeyByType(deleteStack[i].key, deleteStack[i].type) << " | " << maskName(deleteStack[i].name) << "\n";
    }
    cout << "  복구할 번호 입력 (1 = 가장 최근): ";
    int choice;
    if (!(cin >> choice)) { cin.clear(); cin.ignore(1000, '\n'); return; }
    cin.ignore(1000, '\n');

    int si = (int)deleteStack.size() - choice;
    if (si < 0 || si >= (int)deleteStack.size()) { cout << "  [오류] 잘못된 번호입니다.\n"; return; }

    DeletedRecord& rec = deleteStack[si];
    if (rec.type == 1) {
        if (searchTrie(accountRoot, rec.key)) { cout << "  [거부] 이미 존재하는 계좌입니다.\n"; return; }
        // insertTrie가 내부적으로 다시 암호화를 진행하므로 평문을 그대로 넘깁니다.
        insertTrie(accountRoot, rec.key, rec.name, rec.report_date, rec.report_count,
            rec.bank, "-", "-", rec.account, rec.fraud_type, rec.fraud_platform);
    }
    else if (rec.type == 2) {
        if (searchTrie(phoneRoot, rec.key)) { cout << "  [거부] 이미 존재하는 전화번호입니다.\n"; return; }
        insertTrie(phoneRoot, rec.key, rec.name, rec.report_date, rec.report_count,
            "-", "-", rec.phone, "-", rec.fraud_type, rec.fraud_platform);
    }
    else {
        if (searchTrie(emailRoot, rec.key)) { cout << "  [거부] 이미 존재하는 이메일입니다.\n"; return; }
        insertTrie(emailRoot, rec.key, rec.name, rec.report_date, rec.report_count,
            "-", rec.email, "-", "-", rec.fraud_type, rec.fraud_platform);
    }

    FILE* fp = fopen(filename, "a");
    if (fp) {
        fprintf(fp, "%s,%s,%s,%s,\"\"\"%s\"\"\",%s,%s,%s,%s\n",
            rec.name.c_str(), rec.report_date.c_str(), rec.report_count.c_str(),
            rec.bank.c_str(), rec.account.c_str(), rec.email.c_str(), rec.phone.c_str(),
            rec.fraud_type.c_str(), rec.fraud_platform.c_str());
        fclose(fp);
    }
    cout << "  [완료] '" << rec.key << "' 데이터가 완벽하게 복구되었습니다.\n";
    deleteStack.erase(deleteStack.begin() + si);
}

void adminViewAll(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot) {
    cout << "\n=== [Trie 전위순회 전체 데이터 조회] ===\n";
    cout << "\n[1. 사기 계좌번호 목록]\n"; printAllTrie(accountRoot, "", 1);
    cout << "\n[2. 사기 전화번호 목록]\n"; printAllTrie(phoneRoot, "", 2);
    cout << "\n[3. 사기 이메일 목록]\n"; printAllTrie(emailRoot, "", 3);
    cout << "=========================================\n[전위순회 완료]\n";
}

void runAdminMode(TrieNode* accountRoot, TrieNode* phoneRoot, TrieNode* emailRoot,
    const char* filename)
{
    if (!adminLogin()) return;

    int adminChoice;
    while (true) {
        cout << "\n[관리자 통합 제어 메뉴]\n"
            << "  1. 신규 사기 데이터 등록\n"
            << "  2. 등록 데이터 삭제\n"
            << "  3. 전위순회 전체 데이터 조회\n"
            << "  4. 삭제 데이터 복구\n"
            << "  5. 사기 유형/플랫폼 검색\n"
            << "  6. 관리자 모드 종료\n"
            << "  명령 선택: ";

        if (!(cin >> adminChoice)) { cin.clear(); cin.ignore(1000, '\n'); continue; }
        cin.ignore(1000, '\n');

        if (adminChoice == 1)      registerNew(accountRoot, phoneRoot, emailRoot, filename);
        else if (adminChoice == 2) adminDeleteData(accountRoot, phoneRoot, emailRoot);
        else if (adminChoice == 3) adminViewAll(accountRoot, phoneRoot, emailRoot);
        else if (adminChoice == 4) adminUndoDelete(accountRoot, phoneRoot, emailRoot, filename);
        else if (adminChoice == 5) {
            cout << "  검색 기준 선택 (1: 사기유형, 2: 사기플랫폼): ";
            int typeChoice;
            if (!(cin >> typeChoice)) { cin.clear(); cin.ignore(1000, '\n'); continue; }
            cin.ignore(1000, '\n');
            cout << "  검색어 입력: ";
            char keywordRaw[MAX_LINE];
            if (!fgets(keywordRaw, sizeof(keywordRaw), stdin)) continue;
            trimRight(keywordRaw);
            searchByCategory(accountRoot, phoneRoot, emailRoot, keywordRaw, typeChoice == 2);
        }
        else if (adminChoice == 6) { cout << "[관리자 모드 종료]\n"; break; }
        else                       cout << "[오류] 1~6 사이의 값을 입력해 주세요.\n";
    }
}

int main() {
#ifdef _WIN32
    system("chcp 65001 > nul");
    system("cls");
#endif

    cout << "==========================================\n"
        << "   자료구조 기반 사기 데이터 탐지 시스템  \n"
        << "   (Trie 전위순회 + 관리자 모드 포함)     \n"
        << "==========================================\n";

    TrieNode* accountRoot = createTrieNode();
    TrieNode* phoneRoot = createTrieNode();
    TrieNode* emailRoot = createTrieNode();

    loadCSV(accountRoot, phoneRoot, emailRoot, DB_PATH);

    // [보안] 허니팟 트랩 데이터 몰래 삽입 (해커 스캐닝 탐지용, 메모리에만 존재)
    insertTrie(accountRoot, "999999999999", "HONEYPOT_TRAP", "2026-06-06", "999", "미끼은행", "-", "-", "999999999999", "시스템 스캐닝", "-");
    insertTrie(phoneRoot, "01099999999", "HONEYPOT_TRAP", "2026-06-06", "999", "-", "-", "01099999999", "-", "시스템 스캐닝", "-");

    int modeChoice;
    while (true) {
        cout << "\n==========================================\n"
            << "  1. 사용자 모드 (사기 조회 및 텍스트 분석)\n"
            << "  2. 관리자 모드 \n"
            << "  3. 종료\n"
            << "==========================================\n"
            << "모드 선택: ";

        if (!(cin >> modeChoice)) {
            cin.clear(); cin.ignore(1000, '\n');
            cout << "[오류] 숫자로 입력해 주세요.\n"; continue;
        }
        cin.ignore(1000, '\n');

        if (modeChoice == 1) runSearch(accountRoot, phoneRoot, emailRoot, DB_PATH);
        else if (modeChoice == 2) runAdminMode(accountRoot, phoneRoot, emailRoot, DB_PATH);
        else if (modeChoice == 3) { cout << "\n안전하게 종료합니다.\n"; break; }
        else cout << "[오류] 1~3 사이의 값을 입력해 주세요.\n";
    }

    return 0;
}