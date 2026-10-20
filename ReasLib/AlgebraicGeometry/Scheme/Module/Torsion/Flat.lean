module

public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Cover
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine

/-!
# Torsion-freeness of flat scheme modules

Flat quasicoherent modules have torsion-free sections on affine opens.  On an integral scheme,
this sectionwise property gives torsion-freeness of the module sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Sections of a flat quasicoherent `𝒪_X`-module on an affine open are torsion free over the
corresponding ring of functions. -/
theorem IsFlat.torsionFree_sections
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFlat]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  have hflatSections : affineOpenSectionsFlatOver ℱ (𝟙 X) := by
    refine (flatOver_iff_affineOpenSectionsFlatOver ℱ (𝟙 X)).1 ?_
    refine (flatOver_iff_forall_flatOverAt ℱ (𝟙 X)).2 fun x ↦ ?_
    have hstalk : ((𝟙 X : X ⟶ X).stalkMap x).hom =
        RingHom.id (X.presheaf.stalk x) := by
      simpa using congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_id X x)
    let e := (ModuleCat.restrictScalarsId'App
      ((𝟙 X : X ⟶ X).stalkMap x).hom hstalk
      (RingedSpace.stalkModuleCat ℱ x)).symm.toLinearEquiv
    exact (Module.Flat.equiv_iff e).1 (inferInstance : ℱ.IsFlatAt x)
  have hflat : Module.Flat (Γ(X, U)) (Γ(ℱ, U)) := by
    let eU : U ≤ (𝟙 X) ⁻¹ᵁ U := by simp
    have hsections : Scheme.Hom.sectionsMapAlong (𝟙 X) U U eU =
        RingHom.id Γ(X, U) := by
      ext r
      simp only [Scheme.Hom.sectionsMapAlong, Scheme.Hom.appLE,
        Scheme.Hom.id_app, Category.id_comp, CommRingCat.comp_apply,
        CommRingCat.id_apply]
      have he : (homOfLE eU).op = 𝟙 (Opposite.op U) := Subsingleton.elim _ _
      rw [he]
      change (X.presheaf.map (𝟙 (Opposite.op U))).hom r = r
      simpa only [ConcreteCategory.id_apply] using DFunLike.congr_fun
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id (Opposite.op U))) r
    let e := (ModuleCat.restrictScalarsId'App
      (Scheme.Hom.sectionsMapAlong (𝟙 X) U U eU) hsections
      (ModuleCat.of Γ(X, U) Γ(ℱ, U))).symm.toLinearEquiv
    exact (Module.Flat.equiv_iff e).2 (hflatSections hU hU eU)
  exact @Module.Flat.isTorsionFree _ _ _ _ _ hflat

/-- Sections of a flat quasicoherent `𝒪_X`-module on a bundled affine open are torsion free over
the corresponding ring of functions. -/
theorem IsFlat.torsionFree_sections_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFlat]
    (U : X.affineOpens) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  simpa using IsFlat.torsionFree_sections ℱ U.1 U.2

end AlgebraicGeometry.Scheme.Modules

/-- A flat quasicoherent `𝒪_X`-module on an integral scheme is torsion free. -/
theorem AlgebraicGeometry.Scheme.Modules.IsFlat.isTorsionFree
    {X : Scheme.{u}} [IsIntegral X] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFlat] :
    AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ :=
  (AlgebraicGeometry.Scheme.Modules.isTorsionFree_iff_affineOpen ℱ).2
    (AlgebraicGeometry.Scheme.Modules.IsFlat.torsionFree_sections ℱ)

namespace AlgebraicGeometry.Scheme.Modules

/-- Flat quasicoherent `𝒪_X`-modules on integral schemes are canonically torsion free. -/
instance instIsTorsionFreeOfIsFlat
    [IsIntegral X] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFlat] :
    IsTorsionFree ℱ :=
  IsFlat.isTorsionFree ℱ

end AlgebraicGeometry.Scheme.Modules
