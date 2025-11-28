-- The present king of France is bald.

axiom Time : Type
axiom t0 : Time           -- present
axiom FrenchPeople : Type
axiom is_king_at : FrenchPeople → Time → Prop
axiom noKing : ∀(p : FrenchPeople), ¬ is_king_at p t0    -- no present king
axiom is_bald : FrenchPeople → Prop

#print Subtype
-- похоже на Σ-тип
structure Subtype₁ {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
#print Sigma
structure Sigma₁ {α : Type u} (β : α → Type v) where
  mk ::
  fst : α
  snd : β fst

-- Subtype имеет обозначение { x : α // p x }

-- Тогда тип французских королей (зависит от времени):
-- (у Рассела есть условие, что король всего один; мы его опускаем)
def King : Time → Type := λ t => {x : FrenchPeople // is_king_at x t}
#check King

-- тип нынешних королей
def PresentKing := King t0
#check PresentKing


-- тип PresentKing пуст
theorem lem : PresentKing → False := λ ⟨x1,x2⟩ => noKing x1 x2

-- предложение Рассела
def S := ∀ (x : PresentKing), (is_bald x.val)

-- тривиально истинно
theorem tm1 : S := λ x => False.elim (lem x)

-- Рассел формализует через квантор существования, поэтому у него
-- предложение ложно.

def Sᵣ := ∃ x : PresentKing, is_bald x.val

theorem lem3 : (P : α → Prop) → (α → False) → ¬ ∃ x, P x
  | _, n, ⟨fst,_⟩ => n fst

theorem tm2 : Sᵣ → False
| x => lem3 _ lem x

-- Упражнение. Добавьте условие единственности короля.
