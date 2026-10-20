module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ProExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure

/-!
# Distinguished triangles of Deligne systems

This module constructs inverse systems of bounded coherent distinguished triangles whose
vertices are Deligne systems.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X U : Scheme.{v}} (j : U ⟶ X)
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- Restriction of bounded coherent triangles along an open immersion, viewed in the ambient
derived category. -/
noncomputable def restrictionTriangle :
    Pretriangulated.Triangle
        Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] ⥤
      Pretriangulated.Triangle (DerivedCategory U.Modules) :=
  (ambient (SheafOfModules.isCoherent X.ringCatSheaf)).mapTriangle ⋙
    @Functor.mapTriangle _ _ _ _ _ _
      (RingedSpace.modulePullbackDerived j.toShHom)
      (RingedSpace.modulePullbackDerived.commShift j.toShHom)

/-- Restriction along an open immersion sends bounded coherent distinguished triangles to
distinguished triangles in the ambient derived category. -/
theorem restrictionTriangle_obj_distinguished
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (hT : T ∈ Pretriangulated.distinguishedTriangles) :
    (restrictionTriangle j).obj T ∈
      Pretriangulated.distinguishedTriangles := sorry

namespace DeligneSystem

/-- A distinguished bounded coherent triangle on an open subscheme extends to a positive inverse
system of distinguished triangles whose vertices are Deligne systems and whose restriction is
the constant system on the original triangle. -/
theorem exists_triangleSystem
    (T : Pretriangulated.Triangle
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (hT : T ∈ Pretriangulated.distinguishedTriangles) :
    ∃ (S₁ S₂ S₃ : DeligneSystem j)
      (Tₓ : PNatInverseSystem (Pretriangulated.Triangle
        Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])),
      (∀ n : ℕ+, Tₓ.stage n ∈
        distTriang Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) ∧
        Nonempty (Tₓ ⋙ Pretriangulated.Triangle.π₁ ⋙
            ambient (SheafOfModules.isCoherent X.ringCatSheaf) ≅ S₁.tower) ∧
        Nonempty (Tₓ ⋙ Pretriangulated.Triangle.π₂ ⋙
            ambient (SheafOfModules.isCoherent X.ringCatSheaf) ≅ S₂.tower) ∧
        Nonempty (Tₓ ⋙ Pretriangulated.Triangle.π₃ ⋙
            ambient (SheafOfModules.isCoherent X.ringCatSheaf) ≅ S₃.tower) ∧
        Nonempty (Tₓ ⋙ restrictionTriangle j ≅
          (Functor.const (OrderDual ℕ+)).obj
            ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).mapTriangle.obj T)) := sorry

end DeligneSystem

end AlgebraicGeometry.Scheme.ModuleDerived
