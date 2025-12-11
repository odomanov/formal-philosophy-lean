-- списки

#print List

inductive List₁ (α : Type u) where
  | nil : List₁ α
  | cons (head : α) (tail : List₁ α) : List₁ α

#check []
#check 1 :: []
#check 1 :: 5 :: 23 :: []
#check [1, 5, 23]

def tail : List α → List α
| .nil => .nil
| .cons _ xs => xs

#print List.head

def head : (a : List α) → a ≠ [] → α
| .cons x _, _ => x

def head' : List α → (default : α) → α
| [], d => d
| x::_, _ => x

def head'' : List α → Option α
| [] => none
| x::_ => some x

#print Option

-- длина списка
def len : List α → Nat := sorry

#eval len [1,4,0,5]

-- последний элемент
def last : (a : List α) → a ≠ [] → α := sorry

-- добавление в конец
def consr : List α → α → List α := sorry

-- конкатенация
def conc : List α → List α → List α := sorry

#print List.foldl

def foldl {α : Type u} {β : Type v} (f : α → β → α) : (init : α) → List β → α
  | a, .nil      => a
  | a, .cons b l => foldl f (f a b) l

def zip : List α → List β
