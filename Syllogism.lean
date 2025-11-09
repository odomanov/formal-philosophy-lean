-- Силлогизмы.
-- Формы суждения у Аристотеля.

namespace Syllogism

  -- прямая формализация --------

  inductive Judgment : Type 1 where
  | All_are : Type → Type → Judgment
  | Some_are : Type → Type → Judgment

  notation:arg "All"  x "are" y => Judgment.All_are x y
  notation:arg "Some" x "are" y => Judgment.Some_are x y

  -- правила
  inductive T : Judgment → Prop where
  | barbara : T (All A are B) → T (All B are C) → T (All A are C)
  | darii   : T (All A are B) → T (Some C are A) → T (Some C are B)
  -- и т.д.


  -- "непрямая" формализация (вывод правил) --------
  -- В предикатной логике A,E,I,O это ограниченные кванторы.

  axiom E : Type

  -- Утвердительные суждения

  -- AaB
  def all_are (A : E → Prop) (B : E → Prop) : Prop := ∀ x, A x → B x
  notation:arg "all " x " are " y => all_are x y

  -- AiB
  def some_are (A : E → Prop) (B : E → Prop) : Prop := ∃ x, A x ∧ B x
  notation:arg "some " x " are " y => some_are x y

  -- Отрицательные суждения

  -- AeB
  def no_are (A : E → Prop) (B : E → Prop) : Prop := ∀ x, A x → ¬ B x
  notation:arg "no" x " are " y => no_are x y

  -- AoB
  def some_are_not (A : E → Prop) (B : E → Prop) : Prop := ∃ x, A x ∧ ¬ B x
  notation:arg "some" x "are" "not" y => some_are_not x y


  -- некоторые силлогизмы

  def Barbara {A : E → Prop}{B : E → Prop} {C : E → Prop} :
    (all A are B) →
    (all B are C) →
    (all A are C)
    := λ f g => λ x => (g x) ∘ (f x)

  def Darii {A : E → Prop}{B : E → Prop} {C : E → Prop} :
    (all A are B) →
    (some C are A) →
    some C are B
    := λ f ⟨x,⟨cx,ax⟩⟩ => ⟨x,⟨cx,f x ax⟩⟩

  def Celarent {A : E → Prop}{B : E → Prop} {C : E → Prop} :
    (no A are B) →
    (all C are A) →
    no C are B
    := λ f g => λ x => (f x) ∘ (g x)
