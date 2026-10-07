module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import Mathlib.Algebra.Category.ModuleCat.Images

@[expose] public section

open CategoryTheory

universe w v u x

namespace ChowMotive

/-- The Chow group of a motive in degree `i` is the image of its projector under the
degree-`i` realization. -/
def chowGroup {k : Type u} [Field k]
    {GradedCorrespondence : Type u → Type v}
    [Category.{w} (GradedCorrespondence k)]
    (chow : ℤ → GradedCorrespondence k ⥤ ModuleCat.{x} ℚ)
    (M : ChowMotive k GradedCorrespondence) (i : ℤ) : ModuleCat.{x} ℚ :=
  ModuleCat.image ((chow i).map M.p)

/-- The carrier of the Chow group of a motive is the range of the linear action of
its projector under the realization. -/
theorem chowGroup_eq_range {k : Type u} [Field k]
    {GradedCorrespondence : Type u → Type v}
    [Category.{w} (GradedCorrespondence k)]
    (chow : ℤ → GradedCorrespondence k ⥤ ModuleCat.{x} ℚ)
    (M : ChowMotive k GradedCorrespondence) (i : ℤ) :
    chowGroup chow M i =
      ModuleCat.of ℚ (LinearMap.range ((chow i).map M.p).hom) := sorry

end ChowMotive
