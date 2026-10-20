module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Compactification
import StacksCheckRecall

/-!
# Theorem 81.14.9

A separated finite-type algebraic space over a quasi-compact quasi-separated
algebraic space has a compactification over that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Theorem 81.14.9. Let `S` be a scheme. Let `B` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `X ⟶ B` be a separated, finite
type morphism. Then `X` has a compactification over `B`. -/
@[stacks 0F4D] #check
  (AlgebraicGeometry.AlgebraicSpace.HasCompactification.of_finiteType :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [FiniteType f] [Separated f], HasCompactification f)

end AlgebraicGeometry.AlgebraicSpace
