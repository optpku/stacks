module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.HigherDirectImage

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- For a proper morphism of schemes whose scheme-theoretic fibres have dimension
at most `n`, the higher direct images of any locally torsion abelian étale sheaf
vanish in degrees greater than `2 * n`. -/
theorem higherDirectImage_isZero_of_isProper_fiberDimension_le
    {n : ℕ} (hdim : ∀ y : Y, f.fiberDimension y ≤ (n : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (hF : IsLocallyTorsion F)
    {q : ℕ} (hq : 2 * n < q) :
    IsZero (higherDirectImage (smallEtalePullback f) F q :
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end

end
