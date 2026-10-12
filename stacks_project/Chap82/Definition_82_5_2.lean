/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_5_2_AssociatedCycle
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

section

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/- Definition 82.5.2 (1): In Situation 82.2.1, for good `X / B` and a closed
subspace `Y ⊂ X`, the multiplicity of an irreducible component of `Y` is the
length of `𝒪_Y` at its generic point. -/
@[stacks 0EE9]
#check (@ClosedSubspace.componentMultiplicity S X
  (LocallyOfFiniteType.isLocallyNoetherian f) :
    (Y : ClosedSubspace X) → genericPoints Y.X → ℕ)

/- Definition 82.5.2 (2): If `dim_δ(Y) ≤ k`, the associated `k`-cycle is the
multiplicity-weighted sum of the `δ`-dimension-`k` irreducible components of `Y`. -/
@[stacks 0EE9]
#check (Hom.closedSubspaceCycle f δ :
  (Y : ClosedSubspace X) → (k : ℤ) →
    f.closedSubspaceDeltaDimension δ Y ≤ (k : EInt) →
      Function.locallyFinsupp (Points X) ℤ)

end
