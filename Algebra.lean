-- некоторые алгебраические структуры

namespace MyAlgebra

-- класс типов с умножением
class Mul (α : Type u) where
  mul : α → α → α

infix:70 " ● " => Mul.mul

-- класс типов с единицей
class One (α : Type u) where
  one : α

notation "𝟙" => One.one

class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 𝟙 ● a = a
  mul_one : ∀ a : M, a ● 𝟙 = a

-- примеры
instance OneNat : One Nat where
  one := 1
instance MulNat : Mul Nat where
  mul := Nat.mul
instance OneMulNat : MulOneClass Nat where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

instance OneNat' : One Nat where
  one := 0
instance MulNat' : Mul Nat where
  mul := Nat.add
instance OneMulNat' : MulOneClass Nat where
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero


-- НО: не работает. Не те instances
instance OneMulNat'' : MulOneClass Nat where
  -- one := 1
  -- mul := Nat.mul
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

--------------------------------------------

class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, (a ● b) ● c = a ● (b ● c)

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where

-- примеры моноидов

instance NatMulMonoid : Monoid Nat where
  mul := Nat.mul
  one := 1
  mul_assoc := Nat.mul_assoc
  one_mul := by simp
  mul_one := by simp

instance NatMonoid : Monoid Nat where
  mul := Nat.add
  one := 0
  mul_assoc := Nat.add_assoc
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero

instance StrMonoid : Monoid String where
  mul := String.append
  one := ""
  mul_assoc := by simp!
  one_mul := by simp!
  mul_one := by simp!
