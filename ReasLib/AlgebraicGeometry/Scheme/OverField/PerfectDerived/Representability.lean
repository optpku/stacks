module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.GradedObject.Duality
public import ReasLib.CategoryTheory.Pretriangulated.Homological.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded
open scoped CategoryTheory.Pretriangulated.Opposite
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- A proper scheme over a field has bounded coherent representatives for finite-dimensional
homological functors on its opposite perfect derived category. -/
theorem existsBoundedCoherentRepresentation
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (F : (PerfectDerived X)ᵒᵖ ⥤ ModuleCat k)
    [F.IsHomological] [F.Linear k]
    (hF_finite : ∀ E : PerfectDerived X,
      GradedObject.FiniteTotalDimension
        (fun n : ℤ ↦ F.obj (Opposite.op (E⟦n⟧)))) :
    ∃ K : Dᵇ[SheafOfModules.isCoherent X.left.ringCatSheaf],
      Nonempty
        (representedBy X
            ((CohomologyIn.ambient
              (SheafOfModules.isCoherent X.left.ringCatSheaf)).obj K) ≅ F) := sorry

/-- Every linear homological functor on the perfect derived category of a proper regular
scheme over a field, with finite total dimension on all shifts of each perfect complex,
is corepresented by a perfect complex. -/
theorem existsPerfectCorepresentation
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.Regular X.left]
    (G : PerfectDerived X ⥤ ModuleCat k) [G.IsHomological] [G.Linear k]
    (hG_finite : ∀ E : PerfectDerived X,
      GradedObject.FiniteTotalDimension (fun n : ℤ ↦ G.obj (E⟦n⟧))) :
    ∃ K : PerfectDerived X,
      Nonempty ((linearCoyoneda k (PerfectDerived X)).obj (Opposite.op K) ≅ G) := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
