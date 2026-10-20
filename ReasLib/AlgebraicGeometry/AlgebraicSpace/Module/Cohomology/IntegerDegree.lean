module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1

/-!
# Integer-degree cohomology of module sheaves

Étale cohomology of module sheaves is extended by zero in negative degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (F : Modules X)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]

/-- Étale cohomology of a module sheaf in integer degrees, with value zero in negative degrees. -/
def cohomologyInt (q : ℤ) : AddCommGrpCat.{u} :=
  match q with
  | .ofNat n => cohomology X F n
  | .negSucc _ => (HasZeroObject.zero' AddCommGrpCat.{u}).zero

/-- Integer-degree cohomology agrees with ordinary cohomology in nonnegative degrees. -/
@[simp]
theorem cohomologyInt_ofNat (n : ℕ) :
    cohomologyInt X F (Int.ofNat n) = cohomology X F n :=
  rfl

/-- Integer-degree cohomology is the zero abelian group in negative degrees. -/
@[simp]
theorem cohomologyInt_negSucc (n : ℕ) :
    cohomologyInt X F (Int.negSucc n) = (HasZeroObject.zero' AddCommGrpCat.{u}).zero :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
