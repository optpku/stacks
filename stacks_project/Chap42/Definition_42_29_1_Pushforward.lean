/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
  (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (k : ℤ)

/- Compatibility check for proper pushforward after its migration to the reusable Chow-group
owner. -/
#check (AlgebraicGeometry.ChowGroup.map δ X Y f k :
  @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance k →+
    @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) inferInstance k)

end AlgebraicGeometry
