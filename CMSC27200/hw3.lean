import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Basic

structure Change where
  (n₁₀ n₅ n₂ n₁ : Nat)

@[simp]
def Change.amount : Change → Nat
  | ⟨n₁₀, n₅, n₂, n₁⟩ => 10 * n₁₀ + 5 * n₅ + 2 * n₂ + n₁

@[simp]
def Change.count : Change → Nat
  | ⟨n₁₀, n₅, n₂, n₁⟩ => n₁₀ + n₅ + n₂ + n₁

def greedy (n : Nat) : Change :=
  let (n₁₀, r₁) := (n.div 10, n.mod 10)
  let (n₅, r₂) := (r₁.div 5, r₁.mod 5)
  let (n₂, n₁) := (r₂.div 2, r₂.mod 2)
  ⟨n₁₀, n₅, n₂, n₁⟩

def optimal (c : Change) : Prop :=
  ∀ c' : Change, c.amount = c'.amount → c.count ≤ c'.count

def valid (c : Change) (n : Nat) : Prop := optimal c ∧ c.amount = n

@[simp]
def Change.body : Change → Nat
  | ⟨_, n₅, n₂, n₁⟩ => 5 * n₅ + 2 * n₂ + n₁

@[simp]
def Change.tail : Change → Nat
  | ⟨_, _, n₂, n₁⟩ => 2 * n₂ + n₁

lemma amount_n₁₀_body {c : Change} : c.amount = 10 * c.n₁₀ + c.body
    := by simp; linarith

lemma not_optimal {c c' : Change} (h₁ : optimal c)
  (h₂ : c.amount = c'.amount) (h₃ : c'.count < c.count) : False := by
  have h₄ := h₁ c' h₂
  have h₅ := Nat.lt_of_le_of_lt h₄ h₃
  have h₆ := Nat.lt_irrefl c.count
  exact absurd h₅ h₆

lemma optimal_n₁_le_1 {c : Change} (h : optimal c) : c.n₁ ≤ 1 := by
  match h₁ : c.n₁ with
  | 0 => simp
  | 1 => simp
  | n₁' + 2 =>
    let c' : Change := ⟨c.n₁₀, c.n₅, c.n₂ + 1, n₁'⟩
    have h₂ : c.amount = c'.amount := by simp; linarith
    have h₃ : c'.count < c.count := by simp; linarith
    exfalso; exact not_optimal h h₂ h₃

lemma optimal_n₂_le_2 {c : Change} (h : optimal c) : c.n₂ ≤ 2 := by
  match h₁ : c.n₂ with
  | 0 => simp
  | 1 => linarith
  | 2 => linarith
  | n₂' + 3 =>
    let c' : Change := ⟨c.n₁₀, c.n₅ + 1, n₂', c.n₁ + 1⟩
    have h₂ : c.amount = c'.amount := by simp; linarith
    have h₃ : c'.count < c.count := by simp; linarith
    exfalso; exact not_optimal h h₂ h₃

lemma optimal_n₅_le_1 {c : Change} (h : optimal c) : c.n₅ ≤ 1 := by
  match h₁ : c.n₅ with
  | 0 => simp
  | 1 => linarith
  | n₅' + 2 =>
    let c' : Change := ⟨c.n₁₀ + 1, n₅', c.n₂, c.n₁⟩
    have h₂ : c.amount = c'.amount := by simp; linarith
    have h₃ : c'.count < c.count := by simp; linarith
    exfalso; exact not_optimal h h₂ h₃

lemma optimal_n₂_lt_2_or_n₁_lt_1 {c : Change} (h : optimal c) :
    c.n₂ < 2 ∨ c.n₁ < 1 := by
  have h₁ := optimal_n₁_le_1 h
  have h₂ := optimal_n₂_le_2 h
  match h₃ : c.n₁ with
  | 0 => apply Or.inr; linarith
  | 1 => match h₄ : c.n₂ with
    | 0 => apply Or.inl; linarith
    | 1 => apply Or.inl; linarith
    | 2 =>
      let c' : Change := ⟨c.n₁₀, c.n₅ + 1, 0, 0⟩
      have h₅ : c.amount = c'.amount := by simp; linarith
      have h₆ : c'.count < c.count := by simp; linarith
      exfalso; exact not_optimal h h₅ h₆
    | _ + 3 => linarith
  | _ + 2 => linarith

lemma optimal_body_le_9 {c : Change} (h : optimal c) : c.body ≤ 9 := by
  match h₁ : c.n₁ with
  | 0 =>
    have h₂ := optimal_n₂_le_2 h
    have h₃ := optimal_n₅_le_1 h
    simp; linarith
  | 1 =>
    have h₂ := optimal_n₂_le_2 h
    have h₃ := optimal_n₅_le_1 h
    simp
    cases optimal_n₂_lt_2_or_n₁_lt_1 h <;> linarith
  | _ + 2 =>
    have h₃ := optimal_n₁_le_1 h
    linarith

lemma lt_self_sub_1 {n : Nat} : n ≤ n - 1 → n = 0 := by
  intro h₁
  match h₂ : n with
  | 0 => rfl
  | n' + 1 =>
    have h₃ : 1 ≤ n := by linarith
    have h₄ : n ≤ n - 1 ↔ n + 1 ≤ n := Nat.le_sub_iff_add_le h₃
    have h₅ : n' + 1 = n := by linarith
    rw [h₅] at h₁
    have h₆ := h₄.mp h₁
    linarith

lemma mul_div_10 (x y : Nat) : (10 * x + y) / 10 ≥ x := by
  have h₁ : 0 < 10 := by linarith
  have h₂ : x ≤ (10 * x + y) / 10 ↔ x * 10 ≤ 10 * x + y
    := Nat.le_div_iff_mul_le h₁
  rw [ge_iff_le]
  apply h₂.mpr
  linarith

lemma optimal_n₁₀_n_div_10 {c : Change} (h₁ : optimal c)
    (h₂ : n = c.amount): c.n₁₀ = n / 10 := by
  match Nat.lt_trichotomy c.n₁₀ (n / 10) with
  | .inl h₃ =>
    have h₄ : n ≥ 10 := by
      match Nat.eq_zero_or_pos (n / 10) with
      | .inl h₅ => linarith
      | .inr _ =>
        have h₇ : n / 10 ≠ 0 := by linarith
        have h₈ : 10 ≠ 0 := by linarith
        have h₉ := (Nat.div_ne_zero_iff h₈).mp h₇
        assumption
    have h₅ : c.body ≥ 10 := by
      have h₆ := optimal_body_le_9 h₁
      rw [←Nat.succ_le] at h₃
      have h₁₀ : 0 < 10 := by linarith
      have h₁₁ := (Nat.le_div_iff_mul_le h₁₀).mp h₃
      rw [Nat.succ_mul] at h₁₁
      have h₁₂ : c.n₁₀ * 10 ≤ n - 10 := by exact Nat.le_sub_of_add_le h₁₁
      have h₁₃ := Nat.sub_add_cancel h₄
      have h₁₄ := calc n
        _ = c.amount := by rw [h₂]
        _ = 10 * c.n₁₀ + c.body := by rw [amount_n₁₀_body]
        _ ≤ n - 10 + c.body := by linarith
        _ ≤ n - 10 + 9 := by linarith
        _ = n - 1 := by exact eq_tsub_of_add_eq h₁₃
      have h₁₅ := lt_self_sub_1 h₁₄
      linarith
    have h₆ : c.body ≤ 9 := optimal_body_le_9 h₁
    linarith
  | .inr (.inl h₃) => assumption
  | .inr (.inr h₃) =>
    simp at *
    rw [h₂] at h₃
    have h₄ := mul_div_10 c.n₁₀ (5 * c.n₅ + 2 * c.n₂ + c.n₁)
    have h₅ : 10 * c.n₁₀ + (5 * c.n₅ + 2 * c.n₂ + c.n₁)
      = 10 * c.n₁₀ + 5 * c.n₅ + 2 * c.n₂ + c.n₁ := by linarith
    rw [h₅] at h₄
    linarith

lemma optimal_body_n_mod_10 {c : Change} (h₁ : optimal c)
    (h₂ : n = c.amount) : c.body = n % 10 := by
  have h₃ := optimal_n₁₀_n_div_10 h₁ h₂
  have h₄ := Nat.div_add_mod n 10
  rw [amount_n₁₀_body, h₃] at h₂
  have h₅ := Eq.trans h₄ h₂
  linarith

lemma optimal_n₅_n_mod_10_div_5 {c : Change} (h₁ : optimal c)
    (h₂ : n = c.amount) : c.n₅ = (n % 10) / 5 := by
  have h₃ := optimal_body_n_mod_10 h₁ h₂
  simp at h₃
  have h₄ := optimal_n₁_le_1 h₁
  have h₅ := optimal_n₂_le_2 h₁
  have h₆ := optimal_n₂_lt_2_or_n₁_lt_1 h₁
  have h₇ := optimal_n₅_le_1 h₁
  match h₈ : c.n₁ with
  | 0 => match h₉ : c.n₂ with
    | 0 => match h₁₀ : c.n₅ with
      | 0 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | 1 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | n₅' + 2 => linarith
    | 1 => match h₁₀ : c.n₅ with
      | 0 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | 1 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | n₅' + 2 => linarith
    | 2 => match h₁₀ : c.n₅ with
      | 0 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | 1 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | n₅' + 2 => linarith
    | n₂' + 3 => linarith
  | 1 => match h₉ : c.n₂ with
    | 0 => match h₁₀ : c.n₅ with
      | 0 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | 1 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | n₅' + 2 => linarith
    | 1 => match h₁₀ : c.n₅ with
      | 0 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | 1 => rw [h₈, h₉, h₁₀] at h₃; rw [←h₃]; rfl
      | n₅' + 2 => linarith
    | 2 => cases h₆ <;> linarith
    | n₂' + 3 => linarith
  | n₁' + 2 => linarith

lemma mul_mul_mod_mod (a b c d : Nat) :
    (10 * a + 5 * b + 2 * c + d) % 10 % 5
      = (2 * c + d) % 5 := by
  have h₁ : 5 ∣ 10 := by exact Nat.dvd_of_mod_eq_zero rfl
  have h₂ := Nat.mul_add_mod 10 a (5 * b + 2 * c + d)
  have h₃ : 10 * a + (5 * b + 2 * c + d)
    = 10 * a + 5 * b + 2 * c + d := by linarith
  rw [h₃] at h₂
  rw [h₂, Nat.mod_mod_of_dvd (5 * b + 2 * c + d) h₁]
  have h₄ := Nat.mul_add_mod 5 b (2 * c + d)
  have h₅ : 5 * b + (2 * c + d)
    = 5 * b + 2 * c + d := by linarith
  rw [←h₅, h₄]

lemma optimal_n₂_n_mod_10_mod_5_div_2 {c : Change} (h₁ : optimal c)
    (h₂ : n = c.amount) : c.n₂ = n % 10 % 5 / 2 := by
  have h₃ := optimal_n₁_le_1 h₁
  have h₄ := optimal_n₂_le_2 h₁
  have h₅ := optimal_n₂_lt_2_or_n₁_lt_1 h₁
  rw [h₂]
  simp at *
  rw [mul_mul_mod_mod c.n₁₀ c.n₅ c.n₂ c.n₁]
  match h₆ : c.n₁ with
  | 0 => match h₇ : c.n₂ with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n₂' + 3 => linarith
  | 1 => match h₇ : c.n₂ with
    | 0 => rfl
    | 1 => rfl
    | 2 => cases h₅ <;> linarith
    | n₂' + 3 => linarith
  | n₂' + 2 => linarith

lemma optimal_n₁_n_mod_10_mod_5_mod_2 {c : Change} (h₁ : optimal c)
    (h₂ : n = c.amount) : c.n₁ = n % 10 % 5 % 2 := by
  have h₃ := optimal_n₁_le_1 h₁
  have h₄ := optimal_n₂_le_2 h₁
  have h₅ := optimal_n₂_lt_2_or_n₁_lt_1 h₁
  rw [h₂]
  simp at *
  rw [mul_mul_mod_mod c.n₁₀ c.n₅ c.n₂ c.n₁]
  match h₆ : c.n₁ with
  | 0 => match h₇ : c.n₂ with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n₂' + 3 => linarith
  | 1 => match h₇ : c.n₂ with
    | 0 => rfl
    | 1 => rfl
    | 2 => cases h₅ <;> linarith
    | n₂' + 3 => linarith
  | n₂' + 2 => linarith

lemma div_eq (n m : Nat) : Nat.div n m = n / m := rfl
lemma mod_eq (n m : Nat) : Nat.mod n m = n % m := rfl

theorem optimal_eq_greedy {c : Change} (h : optimal c) :
    c = greedy c.amount := by
  let n := c.amount
  have h₂ : n = c.amount := by rfl
  have h₃ := optimal_n₁₀_n_div_10 h h₂
  have h₄ := optimal_n₅_n_mod_10_div_5 h h₂
  have h₅ := optimal_n₂_n_mod_10_mod_5_div_2 h h₂
  have h₆ := optimal_n₁_n_mod_10_mod_5_mod_2 h h₂
  rw [←h₂]
  simp [greedy] at *
  repeat rw [div_eq, mod_eq]
  have h₇ : c = ⟨c.n₁₀, c.n₅, c.n₂, c.n₁⟩ := rfl
  nth_rewrite 1 [h₇]
  nth_rewrite 1 [h₃]
  nth_rewrite 2 [h₄]
  nth_rewrite 3 [h₅]
  nth_rewrite 4 [h₆]
  rfl

theorem optimal_unique (c c' : Change) (h₁ : optimal c) (h₂ : optimal c')
    (h₃ : c.amount = c'.amount): c = c' := by
  have h₄ := optimal_eq_greedy h₁
  have h₅ := optimal_eq_greedy h₂
  rw [h₃] at h₄
  exact Eq.trans h₄ h₅.symm

lemma greedy_amount (n : Nat) : (greedy n).amount = n := by
  simp [greedy]
  repeat rw [div_eq, mod_eq]
  let r₁ := n % 10
  have h₁ : r₁ = n % 10 := rfl
  repeat rw [←h₁]
  have h₂ : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
  nth_rewrite 2 [h₂]
  suffices 5 * (r₁ / 5) + 2 * (r₁ % 5 / 2) + r₁ % 5 % 2 = n % 10 by linarith
  rw [←h₁]
  let r₂ := r₁ % 5
  have h₃ : r₂ = r₁ % 5 := rfl
  repeat rw [←h₃]
  have h₄ : r₂ = 2 * (r₂ / 2) + r₂ % 2 := (Nat.div_add_mod r₂ 2).symm
  rw [Nat.add_assoc, ←h₄, h₃]
  exact Nat.div_add_mod r₁ 5

lemma not_optimal_exists_better {c : Change} (h : ¬optimal c) :
    ∃ c' : Change, c.amount = c'.amount ∧ c'.count < c.count := by
  have ⟨c', h₁⟩ := Classical.not_forall.mp h
  have ⟨h₂, h₃⟩ := not_imp.mp h₁
  exact ⟨c', h₂, Nat.not_le.mp h₃⟩

def recurse_optimal {n : Nat} {c : Change} (k : Nat) (_ : k = c.count)
    (h₂ : n = c.amount) : ∃ c', n = c'.amount ∧ optimal c' :=
  match Classical.em (optimal c) with
  | .inl h₃ => ⟨c, h₂, h₃⟩
  | .inr h₄ =>
    have ⟨c', h₅, _⟩ := not_optimal_exists_better h₄
    have h₇ : n = c'.amount := Eq.trans h₂ h₅
    recurse_optimal c'.count rfl h₇

lemma exists_optimal (n : Nat) : ∃ c, c.amount = n ∧ optimal c := by
  let c := greedy n
  have h₁ := greedy_amount n
  have h₂ : n = Change.amount c := by exact id h₁.symm
  have ⟨c', h₃, h₄⟩ := recurse_optimal c.count rfl h₂
  exact ⟨c', h₃.symm, h₄⟩

lemma greedy_optimal (n : Nat) : optimal (greedy n) := by
  intro c' h
  let ⟨c, h₁, h₂⟩ := exists_optimal n
  have h₃ := optimal_eq_greedy h₂
  rw [h₁] at h₃
  rw [←h₃]
  apply h₂
  rw [←h₃] at h
  assumption

theorem greedy_valid (n : Nat) : valid (greedy n) n :=
  ⟨greedy_optimal n, greedy_amount n⟩
