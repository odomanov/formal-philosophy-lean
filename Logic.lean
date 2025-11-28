-- Логика

namespace Logic

-------------------------------------
--== Пропозициональное равенство ==--

#print Eq
inductive Eq₁ : α → α → Prop where
  | refl (a : α) : Eq₁ a a

#print rfl
def rfl₁ {α : Sort u} {a : α} : Eq a a := Eq.refl a

example : 2 + 3 = 5 := rfl

-- равенство функций
def f1 : Nat → Nat := λ n => n + 2
def f2 : Nat → Nat := (. + 2)
example : f2 = f1 := rfl

----------------------------------
--== пропозициональная логика ==--

-- встроено
theorem proof_irrel {P : Prop} (p q : P) : p = q := rfl

-- импликация это просто функция:
example : ∀ {P Q : Prop}, P → Q → P := sorry




example : ∀ {P Q : Prop}, P → Q → P := λ p => λ _ => p

-- modus ponens
theorem mp : ∀ {P Q : Prop}, (P → Q) → P → Q := sorry




theorem mp₁ : ∀ {P Q : Prop}, (P → Q) → P → Q := fun x => x
theorem mp₂ : ∀ {P Q : Prop}, (P → Q) → P → Q := id

example {P Q : Prop} : P → (P → Q) → Q := λ p pq => mp pq p
example {P Q : Prop} : P → (P → Q) → Q := λ p pq => pq p

-- истина и ложь --

#print True
#print trivial

example : True := True.intro
example : True := .intro
example : True := trivial

#print False

-- конъюнкция --

inductive And₀ (P Q : Prop) : Prop where
| intro : (left : P) → (right : Q) → And₀ P Q

#print And
structure And₁ (P Q : Prop) : Prop where
  intro ::
  left  : P
  right : Q

#check And.intro
#check And₀.intro
#check And.left
#check And.right

#check True ∧ True
example : (True ∧ True) = (And True True) := rfl
example : True ∧ True := And.intro True.intro True.intro
example : True ∧ True := ⟨ True.intro, True.intro ⟩
example : True ∧ True := ⟨ .intro, .intro ⟩
example : True ∧ True := ⟨ trivial, trivial ⟩

#check And.elim

example {P Q : Prop} : P ∧ Q → Q ∧ P := sorry



example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h => ⟨And.right h, And.left h⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h => ⟨h.right, h.left⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h => ⟨h.2, h.1⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ ⟨l,r⟩ => ⟨r,l⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P
  | h => ⟨h.right,h.left⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P
  | ⟨l,r⟩ => ⟨r,l⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := λ h =>
  have hp : P := h.left
  have hq : Q := h.right
  ⟨hq,hp⟩


-- отрицание --

#print Not
def Not₁ (P : Prop) : Prop := P → False

example : ¬ False := fun x => x

#check Not.elim
#check False.elim

-- ex falso quodlibet
example : False → C := False.elim

#check absurd
-- absurd можно доказать
example {P : Prop} {C : Sort u} (h₁ : P) (h₂ : ¬P) : C := sorry

example {P Q R : Prop} : ¬P → Q → (Q → P) → R := sorry

-- modus tolens
theorem mt : ∀ {P Q : Prop}, (P → Q) → ¬ Q → ¬ P := sorry

theorem not_not_intro {P : Prop} : P → ¬ ¬ P := sorry


-- дизъюнкция --

#print Or
inductive Or₁ (a b : Prop) : Prop where
  | inl (h : a) : Or₁ a b
  | inr (h : b) : Or₁ a b

example : True ∨ False := .inl trivial

example {P Q : Prop} (h : P ∨ Q) : Q ∨ P := sorry

#check Or.elim





example {P Q : Prop} (h : P ∨ Q) : Q ∨ P := Or.elim h .inr .inl

example {P Q : Prop} (h : P ∨ Q) : Q ∨ P :=
  Or.elim h
    (fun hp : P => Or.inr hp)
    (fun hq : Q => Or.inl hq)

example {P Q : Prop} (h : P ∨ Q) : Q ∨ P :=
  match h with
  | .inl p => .inr p
  | .inr q => .inl q


-- iff --

#print Iff
structure Iff₁ (P Q : Prop) : Prop where
  intro ::
  mp  : P → Q
  mpr : Q → P

theorem and_swap {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  Iff.intro
    (fun h : P ∧ Q => And.intro (And.right h) (And.left h))   -- P ∧ Q → Q ∧ P
    (fun h : Q ∧ P => And.intro (And.right h) (And.left h))   -- Q ∧ P → P ∧ Q

-- другие варианты записи:

theorem and_swap' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  Iff.intro
    (fun h => ⟨ h.right, h.left ⟩ )   -- P ∧ Q → Q ∧ P
    (fun h => ⟨ h.right, h.left ⟩ )   -- Q ∧ P → P ∧ Q

theorem and_swap'' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

theorem and_swap''' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨ fun ⟨l,r⟩ => ⟨r,l⟩, fun ⟨l,r⟩ => ⟨r,l⟩ ⟩

theorem and_swap'''' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  ⟨ f, f ⟩
  where
  f {X Y : Prop} : X ∧ Y → Y ∧ X := fun h => ⟨h.right, h.left⟩

theorem and_swap''''' {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  let f {X Y : Prop} : X ∧ Y → Y ∧ X := fun h => ⟨h.right, h.left⟩
  ⟨ f, f ⟩


example {P Q : Prop} : (P ↔ Q) → Q → P := sorry



-------------------------------------
--== Пропозициональное равенство ==--

-- Подстановка (в HoTT называется transport)
#check Eq.subst

example (a b : α) (P : α → Prop) (h1 : a = b) (h2 : P a) : P b := h1 ▸ h2

theorem ne_false_of_self {P : Prop} : P → P ≠ False :=
  λ p pf => pf ▸ p

theorem true_ne_false : True ≠ False := sorry

-- равенство это эквивалентность:
theorem refl : ∀ {a : α}, a = a := rfl
theorem symm : ∀ {a b : α}, a = b → b = a := λ x => x ▸ rfl
theorem trans : ∀ {a b c : α}, a = b → b = c → a = c := λ ab bc => bc ▸ ab ▸ rfl

#check Eq.refl
#check Eq.symm
#check Eq.trans

#check congrArg
#check congrFun
#check congr

-- док-во congrArg
example {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂ := h ▸ rfl

-- невозможная функция
example : x = 2 → x = 3 → False := nofun
example : x = 2 → x = 3 → False := λ px py => nomatch px, py

----------------------------
--== логика предикатов  ==--

example {P Q : α → Prop} : (∀ x, P x ∧ Q x) → ∀ y, P y := sorry



example {P Q : α → Prop} : (∀ x, P x ∧ Q x) → ∀ y, P y :=
  λ h : (∀ x, P x ∧ Q x) => λ y : α => (h y).left

#print Exists
inductive Exists₁ {α : Sort u} (P : α → Prop) : Prop where
  | intro (w : α) (h : P w) : Exists₁ P

example : ∃ x, x + 1 = 2 := ⟨1,rfl⟩

#check Exists.elim

example {P Q : α → Prop} (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
    (λ a (pa : P a ∧ Q a) => ⟨a, pa.right, pa.left⟩)

example {P Q : α → Prop} (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  let ⟨x, px, qx⟩ := h
  -- have ⟨x, px, qx⟩ := h
  ⟨x, qx, px⟩

example {P Q : α → Prop} : (h : ∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x
  | ⟨x, px, qx⟩ => ⟨x, qx, px⟩

example {P Q : α → Prop} : (h : ∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x :=
  fun ⟨x, px, qx⟩ => ⟨x, qx, px⟩

-- нужно ли?
example {P Q : α → Prop} (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  ⟨h.choose, h.choose_spec.right, h.choose_spec.left⟩

example {P : α → Prop} {Q : Prop} : (∀ x, P x → Q) → (∃ x, P x) → Q :=
  λ f ep => let ⟨a,pa⟩ := ep; f a pa


-- парадокс брадобрея

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
