namespace Fixture

def Element := Nat

inductive Box where
  | pack : Element → Box

def seed : Box := .pack Nat.zero

inductive Tagged (α : Type) (tag : α) where
  | mk : Tagged α tag

end Fixture
