import tkinter as tk
from tkinter import messagebox, ttk, simpledialog
import csv
import os
import re
from datetime import datetime

ADMIN_CODE = "0000"
DB_PATH = os.path.join(os.path.dirname(__file__), "fraud_search_2", "fraud_accounts_str.csv")

# ============================================================
# 백엔드: Trie 자료구조 및 정규화 기능
# ============================================================
class TrieNode:
    def __init__(self):
        self.isEnd = False
        self.children = {}
        self.name = "-"
        self.report_date = "-"
        self.report_count = "-"
        self.bank = "-"
        self.email = "-"
        self.phone = "-"
        self.account = "-"
        self.fraud_type = "-"
        self.fraud_platform = "-"

class Trie:
    def __init__(self):
        self.root = TrieNode()

    def insert(self, key, name, rd, rc, bank, email, phone, account, fraud_type="-", fraud_platform="-"):
        cur = self.root
        for ch in key:
            if ch not in cur.children:
                cur.children[ch] = TrieNode()
            cur = cur.children[ch]
        cur.isEnd = True
        cur.name = name if name else "-"
        cur.report_date = rd if rd else "-"
        cur.report_count = str(rc) if rc else "1"
        cur.bank = bank if bank else "-"
        cur.email = email if email else "-"
        cur.phone = phone if phone else "-"
        cur.account = account if account else "-"
        cur.fraud_type = fraud_type if fraud_type else "-"
        cur.fraud_platform = fraud_platform if fraud_platform else "-"

    def search(self, key):
        cur = self.root
        for ch in key:
            if ch not in cur.children:
                return None
            cur = cur.children[ch]
        return cur if cur.isEnd else None

    def delete(self, key):
        def _delete_helper(node, key, depth):
            if depth == len(key):
                if node.isEnd:
                    node.isEnd = False
                    return len(node.children) == 0
                return False
            
            ch = key[depth]
            if ch not in node.children:
                return False
            
            should_delete_child = _delete_helper(node.children[ch], key, depth + 1)
            
            if should_delete_child:
                del node.children[ch]
                return not node.isEnd and len(node.children) == 0
            return False
            
        _delete_helper(self.root, key, 0)

    def preorder(self, node=None, prefix="", result_list=None):
        if node is None:
            node = self.root
            if result_list is None:
                result_list = []
        
        if node.isEnd:
            result_list.append({
                "key": prefix,
                "name": node.name,
                "bank": node.bank,
                "report_count": node.report_count,
                "report_date": node.report_date,
                "account": node.account,
                "phone": node.phone,
                "email": node.email,
                "fraud_type": node.fraud_type,
                "fraud_platform": node.fraud_platform
            })
            
        for ch in sorted(node.children.keys()):
            self.preorder(node.children[ch], prefix + ch, result_list)
            
        return result_list

def normalize_number(s):
    return re.sub(r'[^0-9]', '', str(s))

def normalize_email(s):
    return str(s).strip().lower()

def is_phone_number(s):
    num = normalize_number(s)
    return len(num) == 11 and num.startswith("010")

def is_email(s):
    return "@" in str(s)

def is_account_number(s):
    num = normalize_number(s)
    return 10 <= len(num) <= 14

def identify_bank(acc_raw):
    acc = normalize_number(acc_raw)
    length = len(acc)
    if length == 12 and (acc.startswith("110") or acc.startswith("100")): return "신한은행"
    if length == 13 and acc.startswith("1002"): return "우리은행"
    if length == 14 and (acc.startswith("101") or acc.startswith("102") or acc.startswith("620")): return "하나은행"
    if length == 13 and (acc.startswith("301") or acc.startswith("302") or acc.startswith("351") or acc.startswith("352")): return "NH농협은행"
    if length == 14 and acc.startswith("022"): return "KDB산업은행"
    if 10 <= length <= 14: return "국민/기업은행"
    return "미분류"

class FraudDataManager:
    def __init__(self, db_path):
        self.db_path = db_path
        self.account_trie = Trie()
        self.phone_trie = Trie()
        self.email_trie = Trie()
        self.load_csv()

    def load_csv(self):
        if not os.path.exists(self.db_path):
            print(f"[안내] CSV 파일을 찾을 수 없습니다: {self.db_path}")
            return
            
        with open(self.db_path, 'r', encoding='utf-8') as f:
            reader = csv.reader(f)
            header = next(reader, None)
            
            for row in reader:
                if len(row) <= 6:
                    continue
                
                name = row[0].strip() if len(row) > 0 and row[0].strip() else "-"
                rd_raw = row[1].strip() if len(row) > 1 else "-"
                rd = rd_raw.split('|')[-1] if '|' in rd_raw else rd_raw
                
                rc = row[2].strip() if len(row) > 2 and row[2].strip() else "1"
                bank = row[3].strip() if len(row) > 3 and row[3].strip() else "-"
                
                acc_raw = row[4].strip() if len(row) > 4 else ""
                acc_raw = acc_raw.replace('"', '').strip()
                acc = normalize_number(acc_raw)
                
                email_raw = row[5].strip() if len(row) > 5 else ""
                email = normalize_email(email_raw)
                
                phone_raw = row[6].strip() if len(row) > 6 else ""
                phone = normalize_number(phone_raw)
                
                f_type = row[7].strip() if len(row) > 7 else "-"
                f_platform = row[8].strip() if len(row) > 8 else "-"
                
                if acc:
                    self.account_trie.insert(acc, name, rd, rc, bank, "-", "-", acc, f_type, f_platform)
                if phone:
                    self.phone_trie.insert(phone, name, rd, rc, "-", email if email else "-", phone, acc if acc else "-", f_type, f_platform)
                if email:
                    self.email_trie.insert(email, name, rd, rc, "-", email, phone if phone else "-", acc if acc else "-", f_type, f_platform)

    def search_by_category(self, keyword, is_platform=False):
        results = []
        all_nodes = self.account_trie.preorder() + self.phone_trie.preorder() + self.email_trie.preorder()
        seen = set()
        for node in all_nodes:
            target = node['fraud_platform'] if is_platform else node['fraud_type']
            if keyword.lower() in target.lower() and target != "-":
                uniq_id = f"{node['name']}_{node['account']}_{node['phone']}_{node['email']}"
                if uniq_id not in seen:
                    seen.add(uniq_id)
                    results.append(node)
        return results

    def append_to_csv(self, name, rd, rc, bank, acc, email, phone, f_type="-", f_platform="-"):
        acc_fmt = f'"""{acc}"""' if acc and acc != "-" else ""
        file_exists = os.path.exists(self.db_path)
        
        with open(self.db_path, 'a', encoding='utf-8', newline='') as f:
            writer = csv.writer(f)
            if not file_exists:
                writer.writerow(["name", "report_dates", "report_count", "bank", "account_number", "email", "phone", "fraud_type", "fraud_platform"])
            writer.writerow([name, rd, rc, bank, acc_fmt, email, phone, f_type, f_platform])

    def delete_from_csv(self, key, search_type):
        if not os.path.exists(self.db_path):
            return
            
        temp_path = self.db_path + ".tmp"
        with open(self.db_path, 'r', encoding='utf-8') as f, open(temp_path, 'w', encoding='utf-8', newline='') as out:
            reader = csv.reader(f)
            writer = csv.writer(out)
            
            header = next(reader, None)
            if header:
                writer.writerow(header)
                
            for row in reader:
                if len(row) <= 6:
                    writer.writerow(row)
                    continue
                
                is_target = False
                if search_type == "account":
                    acc = normalize_number(row[4].replace('"', ''))
                    if acc == key: is_target = True
                elif search_type == "phone":
                    phone = normalize_number(row[6])
                    if phone == key: is_target = True
                elif search_type == "email":
                    email = normalize_email(row[5])
                    if email == key: is_target = True
                
                if not is_target:
                    writer.writerow(row)
                    
        os.replace(temp_path, self.db_path)


# ============================================================
# 세련된 모던 UI 디자인이 적용된 GUI 클래스
# ============================================================
class FraudSearchApp:
    def __init__(self, root):
        self.root = root
        self.root.title("사기 데이터 탐색 시스템")
        self.root.geometry("600x500")
        self.root.resizable(False, False)

        self.setup_styles()
        self.data_manager = FraudDataManager(DB_PATH)

        self.show_main_screen()

    def setup_styles(self):
        self.style = ttk.Style()
        
        # Windows의 기본 테마 대신 모던한 평면 테마(clam)를 활성화
        if 'clam' in self.style.theme_names():
            self.style.theme_use('clam')
            
        self.bg_color = "#f4f6f9"
        self.primary = "#2c3e50"
        self.accent = "#3498db"
        self.accent_hover = "#2980b9"
        self.danger = "#e74c3c"
        self.danger_hover = "#c0392b"
        
        self.root.configure(bg=self.bg_color)
        
        self.style.configure("TFrame", background=self.bg_color)
        
        self.style.configure("TLabel", background=self.bg_color, font=("맑은 고딕", 11), foreground="#333333")
        self.style.configure("Title.TLabel", font=("맑은 고딕", 22, "bold"), foreground=self.primary)
        self.style.configure("Subtitle.TLabel", font=("맑은 고딕", 13), foreground="#7f8c8d")
        
        self.style.configure("Action.TButton", font=("맑은 고딕", 12, "bold"), background=self.accent, foreground="white", borderwidth=0, padding=12)
        self.style.map("Action.TButton", background=[("active", self.accent_hover)])
                       
        self.style.configure("Danger.TButton", font=("맑은 고딕", 12, "bold"), background=self.danger, foreground="white", borderwidth=0, padding=10)
        self.style.map("Danger.TButton", background=[("active", self.danger_hover)])
                       
        self.style.configure("Outline.TButton", font=("맑은 고딕", 12), background="white", foreground=self.primary, borderwidth=1, bordercolor="#bdc3c7", padding=10)
        self.style.map("Outline.TButton", background=[("active", "#ecf0f1")])

        self.style.configure("TRadiobutton", background=self.bg_color, font=("맑은 고딕", 11), foreground=self.primary)

    def clear_screen(self):
        for widget in self.root.winfo_children():
            widget.destroy()

    def show_main_screen(self):
        self.clear_screen()
        
        main_frame = ttk.Frame(self.root)
        main_frame.pack(expand=True, fill="both", padx=60, pady=70)

        title_label = ttk.Label(main_frame, text="사기 데이터 탐색 시스템", style="Title.TLabel", anchor="center")
        title_label.pack(pady=(10, 5), fill="x")
        
        sub_label = ttk.Label(main_frame, text="안전한 거래를 위한 사전 조회 서비스", style="Subtitle.TLabel", anchor="center")
        sub_label.pack(pady=(0, 50), fill="x")

        user_button = ttk.Button(main_frame, text="🔍 사용자 조회 시작하기", style="Action.TButton", command=self.show_user_screen)
        user_button.pack(fill="x", pady=10)

        admin_button = ttk.Button(main_frame, text="⚙️ 관리자 모드 접속", style="Outline.TButton", command=self.show_admin_login_screen)
        admin_button.pack(fill="x", pady=10)

    def show_user_screen(self):
        self.clear_screen()
        
        frame = ttk.Frame(self.root)
        frame.pack(expand=True, fill="both", padx=40, pady=40)

        title_label = ttk.Label(frame, text="사기 이력 조회", style="Title.TLabel", anchor="center")
        title_label.pack(pady=(10, 20), fill="x")

        self.search_type = tk.StringVar(value="account_number")
        
        radio_frame = ttk.Frame(frame)
        radio_frame.pack(pady=10)
        
        ttk.Radiobutton(radio_frame, text="계좌번호", variable=self.search_type, value="account_number").pack(side="left", padx=10)
        ttk.Radiobutton(radio_frame, text="전화번호", variable=self.search_type, value="phone").pack(side="left", padx=10)
        ttk.Radiobutton(radio_frame, text="이메일", variable=self.search_type, value="email").pack(side="left", padx=10)
        ttk.Radiobutton(radio_frame, text="사기유형", variable=self.search_type, value="fraud_type").pack(side="left", padx=10)
        ttk.Radiobutton(radio_frame, text="사기플랫폼", variable=self.search_type, value="fraud_platform").pack(side="left", padx=10)

        # 예쁜 텍스트 입력창 디자인
        entry_frame = tk.Frame(frame, bg="white", highlightbackground="#bdc3c7", highlightthickness=1, bd=0)
        entry_frame.pack(pady=20, fill="x", padx=20)
        
        search_entry = tk.Entry(entry_frame, font=("맑은 고딕", 14), relief="flat", bg="white", fg=self.primary)
        search_entry.pack(fill="both", expand=True, padx=15, pady=12)

        search_button = ttk.Button(frame, text="조회하기", style="Action.TButton", command=lambda: self.user_search(search_entry.get()))
        search_button.pack(pady=10, fill="x", padx=20)

        back_button = ttk.Button(frame, text="돌아가기", style="Outline.TButton", command=self.show_main_screen)
        back_button.pack(pady=(15, 0), fill="x", padx=20)

    def user_search(self, keyword):
        search_type = self.search_type.get()
        if keyword == "":
            messagebox.showwarning("입력 오류", "조회할 값을 입력하세요.")
            return

        res = None
        key = ""
        
        if search_type == "account_number":
            key = normalize_number(keyword)
            if not is_account_number(key):
                messagebox.showwarning("입력 오류", "계좌번호 형식이 아닙니다. (10~14자리 숫자)")
                return
            res = self.data_manager.account_trie.search(key)
        elif search_type == "phone":
            key = normalize_number(keyword)
            if not is_phone_number(key):
                messagebox.showwarning("입력 오류", "올바른 전화번호 형식이 아닙니다. (010으로 시작하는 11자리 숫자)")
                return
            res = self.data_manager.phone_trie.search(key)
        elif search_type == "email":
            key = normalize_email(keyword)
            if not is_email(key):
                messagebox.showwarning("입력 오류", "올바른 이메일 형식이 아닙니다. (@ 포함)")
                return
            res = self.data_manager.email_trie.search(key)

        if search_type in ["fraud_type", "fraud_platform"]:
            results = self.data_manager.search_by_category(keyword, is_platform=(search_type == "fraud_platform"))
            if results:
                self.show_results_window(results, f"'{keyword}' 검색 결과")
            else:
                messagebox.showinfo("안심 결과", "해당 조건으로 등록된 사기 데이터가 없습니다.")
            return

        if res:
            msg = (
                f"!!! [사기 의심 기록 탐지 성공] !!!\n\n"
                f"성함 : {res.name}\n"
                f"은행 : {res.bank}\n"
                f"계좌번호 : {res.account if res.account != '-' else (key if search_type=='account_number' else '-')}\n"
                f"전화번호 : {res.phone if res.phone != '-' else (key if search_type=='phone' else '-')}\n"
                f"이메일 : {res.email if res.email != '-' else (key if search_type=='email' else '-')}\n"
                f"신고 날짜 : {res.report_date}\n"
                f"신고 횟수 : {res.report_count}"
            )
            messagebox.showwarning("탐지 결과", msg)
        else:
            ans = messagebox.askyesno("안심 결과", "해당 정보는 현재 사기 등록 데이터가 존재하지 않습니다.\n\n사기 의심 정보로 신규 등록하시겠습니까?")
            if ans:
                self.register_new_user(search_type, key)

    def register_new_user(self, search_type, key):
        name = simpledialog.askstring("신규 등록 (1/3)", "피신고자 성함을 입력하세요.\n(모를 경우 빈칸으로 확인)")
        if name is None:
            return
        if name.strip() == "":
            name = "-"

        f_type = simpledialog.askstring("신규 등록 (2/3)", "사기 유형을 입력하세요.\n(예: 보이스피싱, 중고거래 사기 등)\n(모를 경우 빈칸으로 확인)")
        if f_type is None:
            return
        if f_type.strip() == "":
            f_type = "-"

        f_platform = simpledialog.askstring("신규 등록 (3/3)", "사기 플랫폼을 입력하세요.\n(예: 당근마켓, 카카오톡 등)\n(모를 경우 빈칸으로 확인)")
        if f_platform is None:
            return
        if f_platform.strip() == "":
            f_platform = "-"

        rd = datetime.now().strftime("%Y-%m-%d")
        rc = "1"
        bank = "-"
        acc = "-"
        email = "-"
        phone = "-"

        if search_type == "account_number":
            acc = key
            bank = identify_bank(key)
            self.data_manager.account_trie.insert(acc, name, rd, rc, bank, "-", "-", acc, f_type, f_platform)
        elif search_type == "phone":
            phone = key
            self.data_manager.phone_trie.insert(phone, name, rd, rc, "-", email, phone, acc, f_type, f_platform)
        elif search_type == "email":
            email = key
            self.data_manager.email_trie.insert(email, name, rd, rc, "-", email, phone, acc, f_type, f_platform)

        self.data_manager.append_to_csv(name, rd, rc, bank, acc, email, phone, f_type, f_platform)
        messagebox.showinfo("등록 완료", f"{rd} 날짜로 시스템에 등록되었습니다.")


    def show_admin_login_screen(self):
        self.clear_screen()
        
        frame = ttk.Frame(self.root)
        frame.pack(expand=True, fill="both", padx=60, pady=70)

        title_label = ttk.Label(frame, text="관리자 로그인", style="Title.TLabel", anchor="center")
        title_label.pack(pady=(10, 40), fill="x")

        entry_frame = tk.Frame(frame, bg="white", highlightbackground="#bdc3c7", highlightthickness=1, bd=0)
        entry_frame.pack(pady=10, fill="x")
        
        code_entry = tk.Entry(entry_frame, font=("맑은 고딕", 14), relief="flat", bg="white", fg=self.primary, show="●")
        code_entry.pack(fill="both", expand=True, padx=15, pady=12)

        login_button = ttk.Button(frame, text="로그인", style="Action.TButton", command=lambda: self.check_admin_code(code_entry.get()))
        login_button.pack(pady=20, fill="x")

        back_button = ttk.Button(frame, text="처음 화면으로", style="Outline.TButton", command=self.show_main_screen)
        back_button.pack(pady=10, fill="x")

    def check_admin_code(self, code):
        if code == ADMIN_CODE:
            self.show_admin_screen()
        else:
            messagebox.showerror("로그인 실패", "관리자 코드가 올바르지 않습니다.")

    def show_admin_screen(self):
        self.clear_screen()
        
        frame = ttk.Frame(self.root)
        frame.pack(expand=True, fill="both", padx=40, pady=30)

        title_label = ttk.Label(frame, text="관리자 화면", style="Title.TLabel", anchor="center")
        title_label.pack(pady=(10, 10), fill="x")

        info_label = ttk.Label(frame, text="사기 데이터 등록 / 삭제 / 순회", style="Subtitle.TLabel", anchor="center")
        info_label.pack(pady=(0, 20), fill="x")

        view_button = ttk.Button(frame, text="📋 전체 데이터 조회", style="Outline.TButton", command=self.admin_view_all_data)
        view_button.pack(fill="x", pady=8, padx=20)

        add_button = ttk.Button(frame, text="➕ 데이터 등록", style="Outline.TButton", command=self.admin_add_data)
        add_button.pack(fill="x", pady=8, padx=20)

        search_button = ttk.Button(frame, text="🔍 유형/플랫폼 검색", style="Outline.TButton", command=self.admin_category_search)
        search_button.pack(fill="x", pady=8, padx=20)

        delete_button = ttk.Button(frame, text="🗑️ 데이터 삭제", style="Outline.TButton", command=self.admin_delete_data)
        delete_button.pack(fill="x", pady=8, padx=20)

        preorder_button = ttk.Button(frame, text="🔍 전위 순회 확인", style="Outline.TButton", command=self.admin_preorder)
        preorder_button.pack(fill="x", pady=8, padx=20)

        back_button = ttk.Button(frame, text="로그아웃", style="Danger.TButton", command=self.show_main_screen)
        back_button.pack(fill="x", pady=(20, 0), padx=20)

    def admin_view_all_data(self):
        view_window = tk.Toplevel(self.root)
        view_window.title("전체 데이터 조회")
        view_window.geometry("850x450")
        view_window.configure(bg=self.bg_color)
        
        # 스타일 추가
        style = ttk.Style()
        style.configure("Treeview.Heading", font=("맑은 고딕", 11, "bold"), background="#e9ecef", foreground=self.primary)
        style.configure("Treeview", font=("맑은 고딕", 10), rowheight=30)

        tree = ttk.Treeview(view_window, columns=("이름", "신고일자", "신고횟수", "은행", "계좌번호", "이메일", "전화번호", "사기유형", "플랫폼"), show="headings")
        tree.heading("이름", text="이름")
        tree.heading("신고일자", text="신고일자")
        tree.heading("신고횟수", text="신고횟수")
        tree.heading("은행", text="은행")
        tree.heading("계좌번호", text="계좌번호")
        tree.heading("이메일", text="이메일")
        tree.heading("전화번호", text="전화번호")
        tree.heading("사기유형", text="사기유형")
        tree.heading("플랫폼", text="플랫폼")
        
        tree.column("이름", width=80, anchor="center")
        tree.column("신고일자", width=100, anchor="center")
        tree.column("신고횟수", width=60, anchor="center")
        tree.column("은행", width=90, anchor="center")
        tree.column("계좌번호", width=130, anchor="center")
        tree.column("이메일", width=130, anchor="w")
        tree.column("전화번호", width=110, anchor="center")
        tree.column("사기유형", width=90, anchor="center")
        tree.column("플랫폼", width=80, anchor="center")

        tree.pack(fill="both", expand=True, padx=15, pady=15)

        if os.path.exists(DB_PATH):
            with open(DB_PATH, 'r', encoding='utf-8') as f:
                reader = csv.reader(f)
                header = next(reader, None)
                for row in reader:
                    if len(row) > 0:
                        tree.insert("", "end", values=row)

    def admin_add_data(self):
        add_window = tk.Toplevel(self.root)
        add_window.title("데이터 등록")
        add_window.geometry("450x480")
        add_window.configure(bg=self.bg_color)
        
        frame = ttk.Frame(add_window)
        frame.pack(expand=True, fill="both", padx=20, pady=20)
        
        labels = ["유형(1:계좌, 2:전화, 3:이메일)", "성함", "키 값(계좌/전화/이메일)", "신고횟수", "신고날짜(YYYY-MM-DD)"]
        entries = {}
        
        for i, text in enumerate(labels):
            ttk.Label(frame, text=text).grid(row=i, column=0, pady=12, padx=10, sticky="w")
            
            entry_frame = tk.Frame(frame, bg="white", highlightbackground="#bdc3c7", highlightthickness=1, bd=0)
            entry_frame.grid(row=i, column=1, pady=12, padx=10, sticky="ew")
            
            entry = tk.Entry(entry_frame, font=("맑은 고딕", 11), relief="flat", bg="white")
            entry.pack(fill="both", expand=True, padx=5, pady=5)
            entries[text] = entry
            
        entries["신고횟수"].insert(0, "1")
        entries["신고날짜(YYYY-MM-DD)"].insert(0, datetime.now().strftime("%Y-%m-%d"))

        def submit_data():
            type_val = entries["유형(1:계좌, 2:전화, 3:이메일)"].get()
            name = entries["성함"].get() or "-"
            key_val = entries["키 값(계좌/전화/이메일)"].get()
            rc = entries["신고횟수"].get() or "1"
            rd = entries["신고날짜(YYYY-MM-DD)"].get() or datetime.now().strftime("%Y-%m-%d")
            
            if not key_val:
                messagebox.showerror("오류", "키 값을 입력해주세요.")
                return
                
            bank, acc, email, phone = "-", "-", "-", "-"
            
            if type_val == "1":
                acc = normalize_number(key_val)
                if not is_account_number(acc):
                    messagebox.showerror("오류", "유효하지 않은 계좌번호입니다.")
                    return
                if self.data_manager.account_trie.search(acc):
                    messagebox.showerror("거부", "이미 등록된 계좌번호입니다.")
                    return
                bank = identify_bank(acc)
                self.data_manager.account_trie.insert(acc, name, rd, rc, bank, "-", "-", acc)
                
            elif type_val == "2":
                phone = normalize_number(key_val)
                if not is_phone_number(phone):
                    messagebox.showerror("오류", "유효하지 않은 전화번호입니다.")
                    return
                if self.data_manager.phone_trie.search(phone):
                    messagebox.showerror("거부", "이미 등록된 전화번호입니다.")
                    return
                self.data_manager.phone_trie.insert(phone, name, rd, rc, "-", email, phone, acc)
                
            elif type_val == "3":
                email = normalize_email(key_val)
                if not is_email(email):
                    messagebox.showerror("오류", "유효하지 않은 이메일입니다.")
                    return
                if self.data_manager.email_trie.search(email):
                    messagebox.showerror("거부", "이미 등록된 이메일입니다.")
                    return
                self.data_manager.email_trie.insert(email, name, rd, rc, "-", email, phone, acc)
            else:
                messagebox.showerror("오류", "유형은 1, 2, 3 중 하나여야 합니다.")
                return
                
            self.data_manager.append_to_csv(name, rd, rc, bank, acc, email, phone)
            messagebox.showinfo("완료", "등록 완료되었습니다.")
            add_window.destroy()

        submit_btn = ttk.Button(frame, text="✅ 정보 등록", style="Action.TButton", command=submit_data)
        submit_btn.grid(row=len(labels), column=0, columnspan=2, pady=25, sticky="ew")

    def admin_delete_data(self):
        del_key = simpledialog.askstring("데이터 삭제", "삭제할 키워드(계좌번호/전화번호/이메일)를 입력하세요.")
        if not del_key:
            return
            
        if is_email(del_key):
            norm = normalize_email(del_key)
            t = self.data_manager.email_trie.search(norm)
            if not t:
                messagebox.showwarning("결과", "등록되지 않은 이메일입니다.")
                return
            ans = messagebox.askyesno("삭제 확인", f"대상: {t.name} / {norm}\n삭제하시겠습니까?")
            if ans:
                self.data_manager.email_trie.delete(norm)
                self.data_manager.delete_from_csv(norm, "email")
                messagebox.showinfo("완료", "이메일 데이터 삭제 완료")
                
        elif is_phone_number(del_key):
            norm = normalize_number(del_key)
            t = self.data_manager.phone_trie.search(norm)
            if not t:
                messagebox.showwarning("결과", "등록되지 않은 전화번호입니다.")
                return
            ans = messagebox.askyesno("삭제 확인", f"대상: {t.name} / {norm}\n삭제하시겠습니까?")
            if ans:
                self.data_manager.phone_trie.delete(norm)
                self.data_manager.delete_from_csv(norm, "phone")
                messagebox.showinfo("완료", "전화번호 데이터 삭제 완료")
                
        elif is_account_number(del_key):
            norm = normalize_number(del_key)
            t = self.data_manager.account_trie.search(norm)
            if not t:
                messagebox.showwarning("결과", "등록되지 않은 계좌번호입니다.")
                return
            ans = messagebox.askyesno("삭제 확인", f"대상: {t.name} / {norm}\n삭제하시겠습니까?")
            if ans:
                self.data_manager.account_trie.delete(norm)
                self.data_manager.delete_from_csv(norm, "account")
                messagebox.showinfo("완료", "계좌번호 데이터 삭제 완료")
        else:
            messagebox.showerror("오류", "인식할 수 없는 형식입니다.")

    def admin_preorder(self):
        preorder_window = tk.Toplevel(self.root)
        preorder_window.title("전위 순회 확인")
        preorder_window.geometry("700x500")
        preorder_window.configure(bg=self.bg_color)

        text_area = tk.Text(preorder_window, font=("맑은 고딕", 11), wrap="none", bg="white", fg=self.primary, relief="flat", padx=10, pady=10)
        text_area.pack(fill="both", expand=True, padx=20, pady=20)
        
        text_area.insert("end", "=== [Trie 전위순회 전체 데이터 조회] ===\n\n")
        
        def print_trie(title, trie_obj):
            text_area.insert("end", f"[{title}]\n")
            res = trie_obj.preorder(None, "", [])
            if not res:
                text_area.insert("end", "  (데이터 없음)\n")
            for item in res:
                text_area.insert("end", f"  ▶ [{item['key']}]  성함: {item['name']}  |  은행: {item['bank']}  |  신고횟수: {item['report_count']}  |  최근신고일: {item['report_date']}\n")
            text_area.insert("end", "\n")
            
        print_trie("1. 사기 계좌번호 목록", self.data_manager.account_trie)
        print_trie("2. 사기 전화번호 목록", self.data_manager.phone_trie)
        print_trie("3. 사기 이메일 목록", self.data_manager.email_trie)
        
        text_area.insert("end", "=========================================\n")
        text_area.insert("end", "[전위순회 완료]\n")
        text_area.config(state="disabled")

    def show_results_window(self, results, title="검색 결과"):
        view_window = tk.Toplevel(self.root)
        view_window.title(title)
        view_window.geometry("900x450")
        view_window.configure(bg=self.bg_color)
        
        style = ttk.Style()
        style.configure("Treeview.Heading", font=("맑은 고딕", 11, "bold"), background="#e9ecef", foreground=self.primary)
        style.configure("Treeview", font=("맑은 고딕", 10), rowheight=30)

        tree = ttk.Treeview(view_window, columns=("이름", "신고일자", "신고횟수", "은행", "계좌번호", "이메일", "전화번호", "사기유형", "플랫폼"), show="headings")
        tree.heading("이름", text="이름")
        tree.heading("신고일자", text="신고일자")
        tree.heading("신고횟수", text="신고횟수")
        tree.heading("은행", text="은행")
        tree.heading("계좌번호", text="계좌번호")
        tree.heading("이메일", text="이메일")
        tree.heading("전화번호", text="전화번호")
        tree.heading("사기유형", text="사기유형")
        tree.heading("플랫폼", text="플랫폼")
        
        tree.column("이름", width=80, anchor="center")
        tree.column("신고일자", width=100, anchor="center")
        tree.column("신고횟수", width=60, anchor="center")
        tree.column("은행", width=90, anchor="center")
        tree.column("계좌번호", width=130, anchor="center")
        tree.column("이메일", width=130, anchor="w")
        tree.column("전화번호", width=110, anchor="center")
        tree.column("사기유형", width=90, anchor="center")
        tree.column("플랫폼", width=80, anchor="center")

        tree.pack(fill="both", expand=True, padx=15, pady=15)

        for r in results:
            tree.insert("", "end", values=(r['name'], r['report_date'], r['report_count'], r['bank'], r['account'], r['email'], r['phone'], r.get('fraud_type', '-'), r.get('fraud_platform', '-')))

    def admin_category_search(self):
        search_window = tk.Toplevel(self.root)
        search_window.title("사기 유형/플랫폼 검색")
        search_window.geometry("500x250")
        search_window.configure(bg=self.bg_color)
        
        frame = ttk.Frame(search_window)
        frame.pack(expand=True, fill="both", padx=30, pady=30)
        
        search_type = tk.StringVar(value="fraud_type")
        radio_frame = ttk.Frame(frame)
        radio_frame.pack(pady=10)
        ttk.Radiobutton(radio_frame, text="사기 유형", variable=search_type, value="fraud_type").pack(side="left", padx=15)
        ttk.Radiobutton(radio_frame, text="사기 플랫폼", variable=search_type, value="fraud_platform").pack(side="left", padx=15)
        
        entry_frame = tk.Frame(frame, bg="white", highlightbackground="#bdc3c7", highlightthickness=1, bd=0)
        entry_frame.pack(pady=10, fill="x")
        search_entry = tk.Entry(entry_frame, font=("맑은 고딕", 12), relief="flat", bg="white")
        search_entry.pack(fill="both", expand=True, padx=10, pady=8)
        
        def do_search():
            keyword = search_entry.get().strip()
            if not keyword: return
            stype = search_type.get()
            results = self.data_manager.search_by_category(keyword, is_platform=(stype == "fraud_platform"))
            if results:
                self.show_results_window(results, f"관리자: '{keyword}' 검색 결과")
                search_window.destroy()
            else:
                messagebox.showinfo("결과", "해당 조건의 데이터가 없습니다.")
                
        btn = ttk.Button(frame, text="검색", style="Action.TButton", command=do_search)
        btn.pack(pady=10, fill="x")

if __name__ == "__main__":
    root = tk.Tk()
    app = FraudSearchApp(root)
    root.mainloop()