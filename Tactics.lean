-- Тактики
-- https://lean-lang.org/theorem_proving_in_lean4/Tactics/

theorem pqp (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print pqp
theorem pqp' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := ⟨ hp, hq, hp ⟩

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro hq hp
  -- exact And.intro hq hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right => exact And.intro hq hp      -- можно менять порядок
  case left  => exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  and_intros
  · exact hp
  · exact hq
  · exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · assumption
  · apply And.intro hq hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · assumption
  · have h : q ∧ p := ⟨ hq, hp ⟩
    assumption

-- ‹_› -- сокращение для assumption
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · assumption
  · exact ⟨‹q›, ‹p›⟩

example (p q : Prop) (pq : p ∧ q) : q ∧ p := sorry


-- Тактики intro ----------------------------------------------------------

example : ∀ a b c : α, a = b → b = c → a = c := by
  intro a b c ab bc
  rw [ab,bc]
  -- rw [ab]; assumption

example : ∀ a b c : α , a = b → a = c → c = b := by
  intro a b c ab ac
  -- intros
  -- intro _ _ _ ab ac
  apply Eq.trans
  apply Eq.symm
  -- symm               -- тактика для любых симметричных отношений
  assumption
  assumption

#check Eq.trans
#check Eq.symm

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros; subst_eqs; rfl

example (P Q : Prop) : P → Q → P := by
  intros
  assumption

-- modus ponens
example {P Q : Prop} : (P → Q) → P → Q := sorry




example {P Q : Prop} : (P → Q) → P → Q := by
  intros
  apply_assumption
  assumption

-- modus tolens
example {P Q : Prop} : (P → Q) → ¬ Q → ¬ P := sorry




example {P Q : Prop} : (P → Q) → ¬ Q → ¬ P := by
  unfold Not
  intros
  apply_assumption
  apply_assumption
  apply_assumption
  -- repeat apply_assumption


-- intro может сразу разбирать по шаблону
example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨x, hpx, hqx⟩
  exact ⟨x, hqx, hpx⟩

-- даже при нескольких конструкторах
example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨x, Or.inl h⟩ => exact ⟨x, Or.inr h⟩
  | ⟨x, Or.inr h⟩ => exact ⟨x, Or.inl h⟩


-- Тактика revert ----------------------

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption


-- cases ----------------------------

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  · apply Or.inr
    assumption
  · apply Or.inl
    assumption

-- cases с одним конструктором
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; assumption
  -- | intro x px => exists x; exact .inl px
  -- | intro x px => exact ⟨x, .inl px⟩

example (h : a = b) : b = a := by
  cases h with
  | refl => rfl
  -- | _ => rfl
  -- cases h; rfl


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry

open Nat in
example (n : Nat) : pred (succ n) = n := by
  cases n
  · rfl
  · simp

open Nat in
example (n : Nat) (h : n ≠ 0) : (succ (pred n)) = n := sorry


-- cases со сложными выражениями.
-- Nat.lt_or_ge (n m : Nat) : n < m ∨ n ≥ m
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n with
  | inl hlt => exact h₁ hlt
  | inr hge => exact h₂ hge


-- не только для пропозиций:

def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption
#print swap_pair

def swap_pair' : α × β → β × α := λ ⟨x,y⟩ => ⟨y,x⟩

example : swap_pair = swap_pair' := rfl
example : @swap_pair α β = @swap_pair' α β  := rfl

def swap_sum : α ⊕ β → β ⊕ α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption
  -- . rename_i b; exact .inl b

-- rcases - распаковка по шаблону

example : a ∧ b ∧ c ∨ d → a ∨ d := by
  intro h
  rcases h with ⟨ha, hb, hc⟩ | hd
  · exact .inl ha
  · exact .inr hd

example (h : a ∨ b ∨ c ∨ d) : True := by
  rcases h with ha | hb | hc | hd
  repeat trivial

-- использование rfl
example (h : x = 3) (h₂ : x < 4) : x < 4 := by
  rcases h with rfl
  exact h₂


-- Тактика contradiction ----------------------------------------------------------

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

-- равенство конструкторов
example (h : Nat.zero = Nat.succ n) : p := by contradiction

-- инъективность конструкторов
example (h : Nat.succ n = Nat.succ m) : n = m := by injection h

example (h : 2 + 2 = 3) : p := by contradiction
example (h : p) (h' : ¬ p) : q := by contradiction
example (x : Nat) (h : x ≠ x) : p := by contradiction


-- комбинаторы тактик ------------------------

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption


example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

-- try всегда успешна -- repeat (try t) will loop forever !
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)    -- д.б. успешна на всех целях
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor   -- д.б. успешна на хотя бы одной цели
  any_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  -- repeat' constructor
  all_goals assumption


-- rewriting -----

example (x y : Nat) (p : Nat → Prop) (h : y = x) (h' : p x) : p y := by
  rw [h]; assumption

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := sorry

example {a b : Nat} {f : Nat → Nat} (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := sorry



example {a b : Nat} {f : Nat → Nat} (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁]; assumption
  -- rw [←h₁, h₂]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]


-- Тактики simp ----

example : x + 0 = x := by simp
example : p ∧ False ↔ False := by simp


example (x x' y y' : Nat) (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


-- generalize

example : 3 = 3 := by
  generalize 3 = x
  rfl

-- запомнить генерализацию
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

-- show

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

-- сложные тактики

example {P Q : Prop} : (P → Q) → P → Q := by solve_by_elim
example : a = b → b = a := by solve_by_elim
example (a b : Nat) : a + b = b + a := by solve_by_elim

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by solve_by_elim

example {P Q : Prop} : (P → Q) → P → Q := by apply_rules only [*]

example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  apply_rules [Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm]


-- Списки тактик:
--  https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
--  https://github.com/madvorak/lean4-tactics
--  https://hrmacbeth.github.io/math2001/Index_of_Tactics.html
--  https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md
