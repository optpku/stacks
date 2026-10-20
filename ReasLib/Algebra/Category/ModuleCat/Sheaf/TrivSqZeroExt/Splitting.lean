/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt

/-!
# Splitting a square-zero ring-sheaf surjection

A chosen section of a square-zero morphism of commutative ring sheaves identifies the source
with the trivial square-zero extension of the target by the kernel ideal, as sheaves of algebras.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite.TrivSqZeroExt

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TrivSqZeroExt

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O O' : Sheaf J CommRingCat.{w}}

/-- The difference `x - s(proj x)` lies in the sectionwise kernel of `proj`. -/
theorem splittingHomSnd_mem (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (U : Cᵒᵖ) (x : O'.obj.obj U) :
    x - s.hom.app U (proj.hom.app U x) ∈ KernelIdeal.sectionIdeal proj U := sorry

/-- The kernel coordinate of a section of `O'` relative to a chosen splitting of `proj`. -/
def splittingHomSnd (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (U : Cᵒᵖ) (x : O'.obj.obj U) :
    (KernelIdeal.restrict proj s).val.obj U :=
  (KernelIdeal.sectionsIso proj U).inv
    ⟨x - s.hom.app U (proj.hom.app U x), splittingHomSnd_mem proj s hs U x⟩

/-- The forward splitting map on sections: `x ↦ (proj x, x - s(proj x))`. -/
def splittingHomApply (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (U : Cᵒᵖ) (x : O'.obj.obj U) :
    (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.obj U :=
  (proj.hom.app U x, splittingHomSnd proj s hs U x)

/-- The forward splitting map preserves zero. -/
theorem splittingHomApply_zero (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (U : Cᵒᵖ) : splittingHomApply proj s hs U 0 = 0 := sorry

/-- The forward splitting map preserves one. -/
theorem splittingHomApply_one (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (U : Cᵒᵖ) : splittingHomApply proj s hs U 1 = 1 := sorry

/-- The forward splitting map preserves addition. -/
theorem splittingHomApply_add (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (U : Cᵒᵖ) (x y : O'.obj.obj U) :
    splittingHomApply proj s hs U (x + y) =
      splittingHomApply proj s hs U x + splittingHomApply proj s hs U y := sorry

/-- The forward splitting map preserves multiplication when the kernel is square-zero. -/
theorem splittingHomApply_mul (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj) (U : Cᵒᵖ) (x y : O'.obj.obj U) :
    splittingHomApply proj s hs U (x * y) =
      splittingHomApply proj s hs U x * splittingHomApply proj s hs U y := sorry

/-- The component of the forward splitting algebra map over `U`. -/
def splittingHomApp (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj) (U : Cᵒᵖ) :
    O'.obj.obj U ⟶ (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.obj U :=
  CommRingCat.ofHom
    { toFun := splittingHomApply proj s hs U
      map_zero' := splittingHomApply_zero proj s hs U
      map_one' := splittingHomApply_one proj s hs U
      map_add' := splittingHomApply_add proj s hs U
      map_mul' := splittingHomApply_mul proj s hs hI U }

/-- The components of the forward splitting map commute with restriction. -/
theorem splittingHomApp_naturality (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    O'.obj.map rho ≫ splittingHomApp proj s hs hI V =
      splittingHomApp proj s hs hI U ≫
        (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.map rho := sorry

/-- The algebra map `O' ⟶ O ⊕ ℐ` sending `x` to `(proj x, x - s(proj x))`. -/
def splittingHom (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj) :
    O' ⟶ trivSqZeroExt O (KernelIdeal.restrict proj s) :=
  ObjectProperty.homMk
    { app U := splittingHomApp proj s hs hI U
      naturality {U V} rho := splittingHomApp_naturality proj s hs hI rho }

/-- The inverse splitting map on sections: `(a, i) ↦ s(a) + ι(i)`. -/
def splittingInvApply (proj : O' ⟶ O) (s : O ⟶ O') (U : Cᵒᵖ)
    (x : (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.obj U) : O'.obj.obj U :=
  s.hom.app U x.1 + KernelIdeal.restrictedιApp proj s U x.2

/-- The inverse splitting map preserves zero. -/
theorem splittingInvApply_zero (proj : O' ⟶ O) (s : O ⟶ O') (U : Cᵒᵖ) :
    splittingInvApply proj s U 0 = 0 := sorry

/-- The inverse splitting map preserves one. -/
theorem splittingInvApply_one (proj : O' ⟶ O) (s : O ⟶ O') (U : Cᵒᵖ) :
    splittingInvApply proj s U 1 = 1 := sorry

/-- The inverse splitting map preserves addition. -/
theorem splittingInvApply_add (proj : O' ⟶ O) (s : O ⟶ O') (U : Cᵒᵖ)
    (x y : (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.obj U) :
    splittingInvApply proj s U (x + y) =
      splittingInvApply proj s U x + splittingInvApply proj s U y := sorry

/-- The inverse splitting map preserves multiplication when the kernel is square-zero. -/
theorem splittingInvApply_mul (proj : O' ⟶ O) (s : O ⟶ O')
    (hI : KernelIdeal.IsSquareZero proj) (U : Cᵒᵖ)
    (x y : (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.obj U) :
    splittingInvApply proj s U (x * y) =
      splittingInvApply proj s U x * splittingInvApply proj s U y := sorry

/-- The component of the inverse splitting algebra map over `U`. -/
def splittingInvApp (proj : O' ⟶ O) (s : O ⟶ O') (hI : KernelIdeal.IsSquareZero proj)
    (U : Cᵒᵖ) :
    (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.obj U ⟶ O'.obj.obj U :=
  CommRingCat.ofHom
    { toFun := splittingInvApply proj s U
      map_zero' := splittingInvApply_zero proj s U
      map_one' := splittingInvApply_one proj s U
      map_add' := splittingInvApply_add proj s U
      map_mul' := splittingInvApply_mul proj s hI U }

/-- The components of the inverse splitting map commute with restriction. -/
theorem splittingInvApp_naturality (proj : O' ⟶ O) (s : O ⟶ O')
    (hI : KernelIdeal.IsSquareZero proj) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.map rho ≫
        splittingInvApp proj s hI V =
      splittingInvApp proj s hI U ≫ O'.obj.map rho := sorry

/-- The algebra map `O ⊕ ℐ ⟶ O'` sending `(a, i)` to `s(a) + ι(i)`. -/
def splittingInv (proj : O' ⟶ O) (s : O ⟶ O')
    (hI : KernelIdeal.IsSquareZero proj) :
    trivSqZeroExt O (KernelIdeal.restrict proj s) ⟶ O' :=
  ObjectProperty.homMk
    { app U := splittingInvApp proj s hI U
      naturality {U V} rho := splittingInvApp_naturality proj s hI rho }

/-- The forward splitting map followed by `fst` recovers `proj`. -/
theorem splittingHom_comp_fst (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj) :
    splittingHom proj s hs hI ≫ fst O (KernelIdeal.restrict proj s) = proj := sorry

/-- The algebra inclusion followed by the inverse splitting map recovers `s`. -/
theorem splittingInv_comp_inl (proj : O' ⟶ O) (s : O ⟶ O')
    (hI : KernelIdeal.IsSquareZero proj) :
    inl O (KernelIdeal.restrict proj s) ≫ splittingInv proj s hI = s := sorry

/-- The forward splitting map acts by `x ↦ (proj x, x - s(proj x))` on sections. -/
theorem splittingHom_apply (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj) (U : Cᵒᵖ) (x : O'.obj.obj U) :
    (splittingHom proj s hs hI).hom.app U x = splittingHomApply proj s hs U x := sorry

/-- The inverse splitting map acts by `(a, i) ↦ s(a) + ι(i)` on sections. -/
theorem splittingInv_apply (proj : O' ⟶ O) (s : O ⟶ O')
    (hI : KernelIdeal.IsSquareZero proj) (U : Cᵒᵖ)
    (x : (trivSqZeroExt O (KernelIdeal.restrict proj s)).obj.obj U) :
    (splittingInv proj s hI).hom.app U x = splittingInvApply proj s U x := sorry

/-- The forward and inverse splitting maps are inverse on the left. -/
theorem splittingHom_comp_splittingInv (proj : O' ⟶ O) (s : O ⟶ O')
    (hs : s ≫ proj = 𝟙 O) (hI : KernelIdeal.IsSquareZero proj) :
    splittingHom proj s hs hI ≫ splittingInv proj s hI = 𝟙 O' := sorry

/-- The forward and inverse splitting maps are inverse on the right. -/
theorem splittingInv_comp_splittingHom (proj : O' ⟶ O) (s : O ⟶ O')
    (hs : s ≫ proj = 𝟙 O) (hI : KernelIdeal.IsSquareZero proj) :
    splittingInv proj s hI ≫ splittingHom proj s hs hI =
      𝟙 (trivSqZeroExt O (KernelIdeal.restrict proj s)) := sorry

/-- A section of a square-zero ring-sheaf surjection identifies the source with the trivial
square-zero extension of the target by the kernel ideal. -/
def splittingIso (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj) :
    O' ≅ trivSqZeroExt O (KernelIdeal.restrict proj s) where
  hom := splittingHom proj s hs hI
  inv := splittingInv proj s hI
  hom_inv_id := splittingHom_comp_splittingInv proj s hs hI
  inv_hom_id := splittingInv_comp_splittingHom proj s hs hI

end SheafOfModules.RingedSite.TrivSqZeroExt

export SheafOfModules.RingedSite.TrivSqZeroExt (splittingIso)
