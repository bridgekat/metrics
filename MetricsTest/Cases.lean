import MetricsTest.Left
import MetricsTest.Right

namespace Fixture

def pair := (left, right)

theorem conjunction (P Q R : Prop) (hP : P) (hQ : Q) (hR : R) : (P ∧ Q) ∧ R :=
  ⟨⟨hP, hQ⟩, hR⟩

def unused (_skip : Nat) (n : Nat) : Nat := n

end Fixture
