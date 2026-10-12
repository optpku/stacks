/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Degree

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Compatibility check for the degree homomorphism after its migration to the reusable
Chow-group owner. -/
#check (AlgebraicGeometry.ChowGroup.degree :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
        inferInstance 0 →+ ℤ)

end AlgebraicGeometry
