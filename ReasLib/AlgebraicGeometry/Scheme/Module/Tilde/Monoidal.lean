/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import ReasLib.CategoryTheory.Iso.Explicit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal compatibility of affine tilde sheaves

The public comparison maps in this file are constructed from the affine tilde adjunction and the
canonical pure-tensor/internal-Hom section owners.  Invertibility is exposed as an explicit
`IsIso` proposition and is passed to inverse and `*IsoOf` bridges as a certificate.  No global
instance is installed from an unfinished compatibility proof, so non-Prop inverse data never
depends on an ambient `sorry` instance.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}}

namespace Unit

/-- The affine tilde comparison on the tensor unit, in the forward oplax direction. -/
@[stacks 01I8 "affine tilde tensor-unit comparison"]
noncomputable abbrev comparison :
    tilde (ModuleCat.of R R) ⟶ SheafOfModules.unit (Spec R).ringCatSheaf :=
  (tildeSelf (R := R)).hom

/-- The canonical reverse map for the affine tilde tensor-unit comparison. -/
@[stacks 01I8 "reverse affine tilde tensor-unit comparison"]
noncomputable abbrev comparisonInv :
    SheafOfModules.unit (Spec R).ringCatSheaf ⟶ tilde (ModuleCat.of R R) :=
  (tildeSelf (R := R)).inv

/-- The affine tilde tensor-unit comparison as its canonical isomorphism. -/
@[stacks 01I8 "affine tilde tensor-unit comparison isomorphism"]
noncomputable abbrev comparisonIso :
    tilde (ModuleCat.of R R) ≅ SheafOfModules.unit (Spec R).ringCatSheaf :=
  tildeSelf (R := R)

end Unit

/- The affine tensor comparison is built from top-open pure tensors and the tilde adjunction. -/
namespace Tensor

/- The comparison is kept at the forward-map level; no strong-monoidal instance is installed
globally from a deferred invertibility certificate. -/

/-- The value of the affine tensor comparison on a pair of module elements. -/
@[stacks 01I8 "affine tilde tensor comparison on pure elements"]
noncomputable def adjointFun (M N : ModuleCat R) (x : M) (y : N) :
    moduleSpecΓFunctor.obj (tilde M ⊗ tilde N) :=
  SheafOfModules.RingedSite.tensorSection (Spec R).sheaf (Opposite.op ⊤)
    ((tilde.isoTop M).hom x) ((tilde.isoTop N).hom y)

/-- Additivity of the affine tensor comparison in the right module variable. -/
@[stacks 01I8 "additivity of affine tilde tensor sections in the right variable"]
theorem adjointFun_add_right (M N : ModuleCat R) (x : M) (y y' : N) :
    adjointFun M N x (y + y') = adjointFun M N x y + adjointFun M N x y' := sorry

/-- Scalar compatibility of the affine tensor comparison in the right module variable. -/
@[stacks 01I8 "scalar compatibility of affine tilde tensor sections in the right variable"]
theorem adjointFun_smul_right (M N : ModuleCat R) (x : M) (r : R) (y : N) :
    adjointFun M N x (r • y) = r • adjointFun M N x y := sorry

/-- Additivity of the affine tensor comparison in the left module variable. -/
@[stacks 01I8 "additivity of affine tilde tensor sections in the left variable"]
theorem adjointFun_add_left (M N : ModuleCat R) (x x' : M) (y : N) :
    adjointFun M N (x + x') y = adjointFun M N x y + adjointFun M N x' y := sorry

/-- Scalar compatibility of the affine tensor comparison in the left module variable. -/
@[stacks 01I8 "scalar compatibility of affine tilde tensor sections in the left variable"]
theorem adjointFun_smul_left (M N : ModuleCat R) (r : R) (x : M) (y : N) :
    adjointFun M N (r • x) y = r • adjointFun M N x y := sorry

/-- Right-linear pure tensoring of affine global sections. -/
@[stacks 01I8 "right-linear affine tilde tensor section map"]
noncomputable def adjointRight (M N : ModuleCat R) (x : M) :
    N →ₗ[R] moduleSpecΓFunctor.obj (tilde M ⊗ tilde N) where
  toFun := adjointFun M N x
  map_add' := adjointFun_add_right M N x
  map_smul' := adjointFun_smul_right M N x

/-- Additivity of right-linear affine tensoring in its fixed left element. -/
@[stacks 01I8 "additivity of right-linear affine tilde tensoring"]
theorem adjointRight_add_left (M N : ModuleCat R) (x x' : M) :
    adjointRight M N (x + x') = adjointRight M N x + adjointRight M N x' := sorry

/-- Scalar compatibility of right-linear affine tensoring in its fixed left element. -/
@[stacks 01I8 "scalar compatibility of right-linear affine tilde tensoring"]
theorem adjointRight_smul_left (M N : ModuleCat R) (r : R) (x : M) :
    adjointRight M N (r • x) = r • adjointRight M N x := sorry

/-- The bilinear map whose tensor-product lift defines affine tilde's canonical comparison. -/
@[stacks 01I8 "bilinear affine tilde tensor comparison"]
noncomputable def adjointBilinear (M N : ModuleCat R) :
    M →ₗ[R] N →ₗ[R] moduleSpecΓFunctor.obj (tilde M ⊗ tilde N) where
  toFun := adjointRight M N
  map_add' := adjointRight_add_left M N
  map_smul' := adjointRight_smul_left M N

/-- The global-sections morphism adjoint to affine tilde's tensor comparison. -/
@[stacks 01I8 "adjoint affine tilde tensor comparison"]
noncomputable def adjoint (M N : ModuleCat R) :
    (M ⊗ N : ModuleCat R) ⟶ moduleSpecΓFunctor.obj (tilde M ⊗ tilde N) :=
  ModuleCat.TensorProduct.lift R (adjointBilinear M N)

/-- The tensor adjoint evaluates on a pure tensor by the explicit section map. -/
@[simp, stacks 01I8 "pure-tensor formula for affine tilde tensor adjoint"]
theorem adjoint_apply (M N : ModuleCat R) (x : M) (y : N) :
    (adjoint M N).hom (x ⊗ₜ[R] y) = adjointFun M N x y := sorry

/-- The canonical comparison from tilde of a tensor product to the tensor product of tilde
sheaves. -/
@[stacks 01I8 "affine tilde tensor comparison"]
noncomputable def comparison (M N : ModuleCat R) :
    tilde (M ⊗ N : ModuleCat R) ⟶ tilde M ⊗ tilde N :=
  (tilde.adjunction.homEquiv _ _).symm (adjoint M N)

/-- The adjunction transpose recovers the defining affine tensor section map. -/
@[simp, stacks 01I8 "adjunction transpose of affine tilde tensor comparison"]
theorem homEquiv_comparison (M N : ModuleCat R) :
    tilde.adjunction.homEquiv _ _ (comparison M N) = adjoint M N := sorry

/-- Naturality of the affine tensor comparison in both module variables. -/
@[stacks 01I8 "naturality of affine tilde tensor comparison"]
theorem naturality {M M' N N' : ModuleCat R} (f : M ⟶ M') (g : N ⟶ N') :
    (tilde.functor R).map (f ⊗ₘ g) ≫ comparison M' N' =
      comparison M N ≫ ((tilde.functor R).map f ⊗ₘ (tilde.functor R).map g) := sorry

/-- The affine tensor comparisons form a natural transformation. -/
@[stacks 01I8 "natural affine tilde tensor comparison"]
noncomputable def comparisonNatTrans (R : CommRingCat.{u}) :
    MonoidalCategory.tensor (ModuleCat.{u} R) ⋙ tilde.functor R ⟶
      Functor.prod (tilde.functor R) (tilde.functor R) ⋙
        MonoidalCategory.tensor (Spec R).Modules where
  app MN := comparison MN.1 MN.2
  naturality := fun {X Y} f => Tensor.naturality f.1 f.2

/-- A component of the affine tensor natural transformation is the canonical comparison. -/
@[simp, stacks 01I8 "component of natural affine tilde tensor comparison"]
theorem comparisonNatTrans_app (MN : ModuleCat R × ModuleCat R) :
    (comparisonNatTrans R).app MN = comparison MN.1 MN.2 := sorry

/-- The affine tensor comparison is invertible.  Downstream inverse bridges take this proposition
as an explicit certificate. -/
@[stacks 01I8 "invertibility of affine tilde tensor comparison"]
theorem comparisonIsIso (M N : ModuleCat R) : IsIso (comparison M N) := sorry

/-- The inverse of the affine tensor comparison obtained from its available invertibility
certificate. -/
@[stacks 01I8 "explicit inverse of affine tilde tensor comparison"]
noncomputable def comparisonInv (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    tilde M ⊗ tilde N ⟶ tilde (M ⊗ N : ModuleCat R) :=
  h.toIso.inv

/-- The affine tensor comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01I8 "affine tilde tensor comparison inverse law"]
theorem comparison_comp_comparisonInv (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    comparison M N ≫ comparisonInv M N h = 𝟙 _ := sorry

/-- The explicit inverse of the affine tensor comparison followed by the comparison is the
identity. -/
@[simp, stacks 01I8 "affine tilde tensor comparison inverse law"]
theorem comparisonInv_comp_comparison (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    comparisonInv M N h ≫ comparison M N = 𝟙 _ := sorry

/-- The inverse affine tensor comparisons are natural in both module variables. -/
@[stacks 01I8 "naturality of inverse affine tilde tensor comparison"]
theorem comparisonInv_naturality {M M' N N' : ModuleCat R}
    (f : M ⟶ M') (g : N ⟶ N')
    (hMN : IsIso (comparison M N)) (hM'N' : IsIso (comparison M' N')) :
    ((tilde.functor R).map f ⊗ₘ (tilde.functor R).map g) ≫ comparisonInv M' N' hM'N' =
      comparisonInv M N hMN ≫ (tilde.functor R).map (f ⊗ₘ g) := sorry

/-- Bundle the affine tensor comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit affine tilde tensor comparison isomorphism"]
noncomputable def comparisonIsoOf (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    tilde (M ⊗ N : ModuleCat R) ≅ tilde M ⊗ tilde N :=
  h.toIso

/-- Pointwise invertibility of the affine tensor comparison transformation. -/
@[stacks 01I8 "invertibility of natural affine tilde tensor comparison"]
theorem comparisonNatTrans_isIso (R : CommRingCat.{u}) :
    IsIso (comparisonNatTrans R) := sorry

/-- Bundle the natural affine tensor comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit natural affine tilde tensor comparison isomorphism"]
noncomputable def comparisonNatIsoOf (R : CommRingCat.{u})
    (h : IsIso (comparisonNatTrans R)) :
    MonoidalCategory.tensor (ModuleCat.{u} R) ⋙ tilde.functor R ≅
      Functor.prod (tilde.functor R) (tilde.functor R) ⋙
        MonoidalCategory.tensor (Spec R).Modules :=
  h.toIso

end Tensor

namespace TensorPower

/-- The canonical comparison from tilde of a module tensor power to the corresponding
ringed-space tensor power of its affine tilde sheaf. -/
@[stacks 01I8 "affine tilde ringed-space tensor-power comparison"]
noncomputable def comparison (M : ModuleCat R) : (n : ℕ) →
    tilde (tensorPower M n) ⟶
      (RingedSpace.TensorPower.sheaf (tilde M) n : (Spec R).Modules) :=
  fun
  | 0 => (tildeSelf (R := R)).hom
  | n + 1 => Tensor.comparison M (tensorPower M n) ≫
      (𝟙 (tilde M) ⊗ₘ comparison M n)

/-- The affine tilde ringed-space tensor-power comparison is natural in the module. -/
@[stacks 01I8 "naturality of affine tilde ringed-space tensor-power comparison"]
theorem naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ) :
    (tilde.functor R).map (tensorPowerMap f n) ≫ comparison N n =
      comparison M n ≫
        RingedSpace.TensorPower.map ((tilde.functor R).map f) n := sorry

/- The recursion is exposed separately so downstream proofs can use the canonical map without an
inverse. -/

/-- The zero-degree tensor-power comparison is the affine structure-module identification. -/
@[simp, stacks 01I8 "zero-degree affine tilde tensor-power comparison"]
theorem comparison_zero (M : ModuleCat R) :
    comparison M 0 = (tildeSelf (R := R)).hom := sorry

/-- The successor tensor-power comparison is obtained by tensoring the preceding comparison. -/
@[simp, stacks 01I8 "successor affine tilde tensor-power comparison"]
theorem comparison_succ (M : ModuleCat R) (n : ℕ) :
    comparison M (n + 1) = Tensor.comparison M (tensorPower M n) ≫
      (𝟙 (tilde M) ⊗ₘ comparison M n) := sorry

/-- The canonical affine tensor-power comparison is invertible. -/
@[stacks 01I8 "invertibility of affine tilde tensor-power comparison"]
theorem comparisonIsIso (M : ModuleCat R) (n : ℕ) : IsIso (comparison M n) := sorry

/-- The inverse of the affine tensor-power comparison obtained from its available invertibility
certificate. -/
@[stacks 01I8 "explicit inverse of affine tilde tensor-power comparison"]
noncomputable def comparisonInv (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    (RingedSpace.TensorPower.sheaf (tilde M) n : (Spec R).Modules) ⟶
      tilde (tensorPower M n) :=
  h.toIso.inv

/-- The affine tensor-power comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01I8 "affine tilde tensor-power comparison inverse law"]
theorem comparison_comp_comparisonInv (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    comparison M n ≫ comparisonInv M n h = 𝟙 _ := sorry

/-- The explicit inverse of the affine tensor-power comparison followed by the comparison is the
identity. -/
@[simp, stacks 01I8 "affine tilde tensor-power comparison inverse law"]
theorem comparisonInv_comp_comparison (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    comparisonInv M n h ≫ comparison M n = 𝟙 _ := sorry

/-- The inverse affine tensor-power comparisons are natural in the module. -/
@[stacks 01I8 "naturality of inverse affine tilde tensor-power comparison"]
theorem comparisonInv_naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ)
    (hM : IsIso (comparison M n)) (hN : IsIso (comparison N n)) :
    RingedSpace.TensorPower.map ((tilde.functor R).map f) n ≫ comparisonInv N n hN =
      comparisonInv M n hM ≫ (tilde.functor R).map (tensorPowerMap f n) := sorry

/-- Bundle the affine tensor-power comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit affine tilde tensor-power comparison isomorphism"]
noncomputable def comparisonIsoOf (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    tilde (tensorPower M n) ≅
      (RingedSpace.TensorPower.sheaf (tilde M) n : (Spec R).Modules) :=
  h.toIso

/-- The affine tensor-power comparisons form a natural transformation in each degree. -/
@[stacks 01I8 "natural affine tilde tensor-power comparison"]
noncomputable def comparisonNatTrans (R : CommRingCat.{u}) (n : ℕ) :
    tensorPowerFunctor (ModuleCat.{u} R) n ⋙ tilde.functor R ⟶
      tilde.functor R ⋙ RingedSpace.TensorPower.functor (Spec R).toRingedSpace n where
  app M := comparison M n
  naturality := fun {M N} f => TensorPower.naturality f n

/-- A component of the affine tensor-power natural transformation is the canonical comparison. -/
@[simp, stacks 01I8 "component of natural affine tilde tensor-power comparison"]
theorem comparisonNatTrans_app (M : ModuleCat R) (n : ℕ) :
    (comparisonNatTrans R n).app M = comparison M n := sorry

/-- The affine tensor-power comparison transformation is pointwise invertible. -/
@[stacks 01I8 "invertibility of natural affine tilde tensor-power comparison"]
theorem comparisonNatTrans_isIso (R : CommRingCat.{u}) (n : ℕ) :
    IsIso (comparisonNatTrans R n) := sorry

/-- Bundle the natural affine tensor-power comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit natural affine tensor-power comparison isomorphism"]
noncomputable def comparisonNatIsoOf (R : CommRingCat.{u}) (n : ℕ)
    (h : IsIso (comparisonNatTrans R n)) :
    tensorPowerFunctor (ModuleCat.{u} R) n ⋙ tilde.functor R ≅
      tilde.functor R ⋙ RingedSpace.TensorPower.functor (Spec R).toRingedSpace n :=
  h.toIso

end TensorPower

namespace SymmetricPower

/-- The adjoint global-sections map defining the affine tilde symmetric-power comparison.  It
first takes symmetric powers of the affine global-sections comparison, respecting the scalar map
`R ⟶ Γ(Spec R, 𝒪)`, and then applies the module-sheafification unit on the top open. -/
@[stacks 01I8 "adjoint affine tilde symmetric-power comparison"]
noncomputable def adjoint (M : ModuleCat R) (n : ℕ) :
    M.symmetricPower n ⟶ moduleSpecΓFunctor.obj (Sym[n] (tilde M)) :=
  ModuleCat.symmetricPower.mapRestrictScalars
      (Scheme.ΓSpecIso R).inv.hom (tilde.isoTop M).hom n ≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).map
      ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal (Spec R).sheaf
        (RingedSpace.SymmetricPower.presheaf (tilde M) n)).app (Opposite.op ⊤))

/-- The adjoint affine tilde symmetric-power comparison is natural in the module. -/
@[stacks 01I8 "naturality of adjoint affine tilde symmetric-power comparison"]
theorem adjoint_naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ) :
    ModuleCat.symmetricPower.map f n ≫ adjoint N n =
      adjoint M n ≫
        moduleSpecΓFunctor.map
          (RingedSpace.SymmetricPower.map ((tilde.functor R).map f) n) := sorry

/-- The canonical comparison from tilde of a module symmetric power to the symmetric-power sheaf
of its affine tilde sheaf. -/
@[stacks 01I8 "affine tilde symmetric-power comparison"]
noncomputable def comparison (M : ModuleCat R) (n : ℕ) :
    tilde (M.symmetricPower n) ⟶ (Sym[n] (tilde M) : (Spec R).Modules) :=
  (tilde.adjunction.homEquiv _ _).symm (adjoint M n)

/-- Transposing the affine tilde symmetric-power comparison recovers its defining
global-sections map. -/
@[simp, stacks 01I8 "adjunction transpose of affine tilde symmetric-power comparison"]
theorem homEquiv_comparison (M : ModuleCat R) (n : ℕ) :
    tilde.adjunction.homEquiv _ _ (comparison M n) = adjoint M n := sorry

/-- The affine tilde symmetric-power comparison is natural in the module. -/
@[stacks 01I8 "naturality of affine tilde symmetric-power comparison"]
theorem naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ) :
    (tilde.functor R).map (ModuleCat.symmetricPower.map f n) ≫ comparison N n =
      comparison M n ≫
        RingedSpace.SymmetricPower.map ((tilde.functor R).map f) n := sorry

/-- The canonical affine tilde symmetric-power comparison is invertible.  Its proposition is
passed explicitly to inverse bridges. -/
@[stacks 01I8 "invertibility of affine tilde symmetric-power comparison"]
theorem comparisonIsIso (M : ModuleCat R) (n : ℕ) :
    IsIso (comparison M n) := sorry

/-- The inverse of the affine symmetric-power comparison obtained from its available invertibility
certificate. -/
@[stacks 01I8 "explicit inverse of affine tilde symmetric-power comparison"]
noncomputable def comparisonInv (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    (Sym[n] (tilde M) : (Spec R).Modules) ⟶ tilde (M.symmetricPower n) :=
  h.toIso.inv

/-- The affine symmetric-power comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01I8 "affine tilde symmetric-power comparison inverse law"]
theorem comparison_comp_comparisonInv (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    comparison M n ≫ comparisonInv M n h = 𝟙 _ := sorry

/-- The explicit inverse of the affine symmetric-power comparison followed by the comparison is the
identity. -/
@[simp, stacks 01I8 "affine tilde symmetric-power comparison inverse law"]
theorem comparisonInv_comp_comparison (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    comparisonInv M n h ≫ comparison M n = 𝟙 _ := sorry

/-- The inverse affine symmetric-power comparisons are natural in the module. -/
@[stacks 01I8 "naturality of inverse affine tilde symmetric-power comparison"]
theorem comparisonInv_naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ)
    (hM : IsIso (comparison M n)) (hN : IsIso (comparison N n)) :
    RingedSpace.SymmetricPower.map ((tilde.functor R).map f) n ≫ comparisonInv N n hN =
      comparisonInv M n hM ≫
        (tilde.functor R).map (ModuleCat.symmetricPower.map f n) := sorry

/-- Bundle the affine symmetric-power comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit affine tilde symmetric-power comparison isomorphism"]
noncomputable def comparisonIsoOf (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    tilde (M.symmetricPower n) ≅ (Sym[n] (tilde M) : (Spec R).Modules) :=
  h.toIso

/-- The affine tilde symmetric-power comparisons form a natural transformation. -/
@[stacks 01I8 "natural comparison for affine tilde symmetric powers"]
noncomputable def comparisonNatTrans (R : CommRingCat.{u}) (n : ℕ) :
    ModuleCat.symmetricPower.functor R n ⋙ tilde.functor R ⟶
      tilde.functor R ⋙ RingedSpace.SymmetricPower.functor (Spec R).toRingedSpace n where
  app M := comparison M n
  naturality := fun {M N} f => SymmetricPower.naturality f n

/-- A component of the affine tilde symmetric-power natural transformation is the canonical
comparison. -/
@[simp, stacks 01I8 "component of the affine tilde symmetric-power natural comparison"]
theorem comparisonNatTrans_app (M : ModuleCat R) (n : ℕ) :
    (comparisonNatTrans R n).app M = comparison M n := sorry

/-- The affine tilde symmetric-power natural comparison is pointwise invertible; its proposition is
available as an explicit certificate for the natural isomorphism bridge. -/
@[stacks 01I8 "invertibility of the affine tilde symmetric-power natural comparison"]
theorem comparisonNatTrans_isIso (R : CommRingCat.{u}) (n : ℕ) :
    IsIso (comparisonNatTrans R n) := sorry

/-- Bundle the natural affine symmetric-power comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit natural affine tilde symmetric-power comparison isomorphism"]
noncomputable def comparisonNatIsoOf (R : CommRingCat.{u}) (n : ℕ)
    (h : IsIso (comparisonNatTrans R n)) :
    ModuleCat.symmetricPower.functor R n ⋙ tilde.functor R ≅
      tilde.functor R ⋙ RingedSpace.SymmetricPower.functor (Spec R).toRingedSpace n :=
  h.toIso

end SymmetricPower

namespace ExteriorPower

/-- The adjoint global-sections map defining the affine tilde exterior-power comparison.  It
first takes exterior powers of the affine global-sections comparison, respecting the scalar map
`R ⟶ Γ(Spec R, 𝒪)`, and then applies the module-sheafification unit on the top open. -/
@[stacks 01I8 "adjoint affine tilde exterior-power comparison"]
noncomputable def adjoint (M : ModuleCat R) (n : ℕ) :
    M.exteriorPower n ⟶ moduleSpecΓFunctor.obj (Λ[n] (tilde M)) :=
  ModuleCat.exteriorPower.mapRestrictScalars
      (Scheme.ΓSpecIso R).inv.hom (tilde.isoTop M).hom n ≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).map
      ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal (Spec R).sheaf
        (RingedSpace.ExteriorPower.presheaf (tilde M) n)).app (Opposite.op ⊤))

/-- The adjoint affine tilde exterior-power comparison is natural in the module. -/
@[stacks 01I8 "naturality of adjoint affine tilde exterior-power comparison"]
theorem adjoint_naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ) :
    ModuleCat.exteriorPower.map f n ≫ adjoint N n =
      adjoint M n ≫
        moduleSpecΓFunctor.map
          (RingedSpace.ExteriorPower.map ((tilde.functor R).map f) n) := sorry

/-- The canonical comparison from tilde of a module exterior power to the exterior-power sheaf
of its affine tilde sheaf. -/
@[stacks 01I8 "affine tilde exterior-power comparison"]
noncomputable def comparison (M : ModuleCat R) (n : ℕ) :
    tilde (M.exteriorPower n) ⟶ (Λ[n] (tilde M) : (Spec R).Modules) :=
  (tilde.adjunction.homEquiv _ _).symm (adjoint M n)

/-- Transposing the affine tilde exterior-power comparison recovers its defining global-sections
map. -/
@[simp, stacks 01I8 "adjunction transpose of affine tilde exterior-power comparison"]
theorem homEquiv_comparison (M : ModuleCat R) (n : ℕ) :
    tilde.adjunction.homEquiv _ _ (comparison M n) = adjoint M n := sorry

/-- The affine tilde exterior-power comparison is natural in the module. -/
@[stacks 01I8 "naturality of affine tilde exterior-power comparison"]
theorem naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ) :
    (tilde.functor R).map (ModuleCat.exteriorPower.map f n) ≫ comparison N n =
      comparison M n ≫
        RingedSpace.ExteriorPower.map ((tilde.functor R).map f) n := sorry

/-- The canonical affine tilde exterior-power comparison is invertible.  Its proposition is
passed explicitly to inverse bridges. -/
@[stacks 01I8 "invertibility of affine tilde exterior-power comparison"]
theorem comparisonIsIso (M : ModuleCat R) (n : ℕ) :
    IsIso (comparison M n) := sorry

/-- The inverse of the affine exterior-power comparison obtained from its available invertibility
certificate. -/
@[stacks 01I8 "explicit inverse of affine tilde exterior-power comparison"]
noncomputable def comparisonInv (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    (Λ[n] (tilde M) : (Spec R).Modules) ⟶ tilde (M.exteriorPower n) :=
  h.toIso.inv

/-- The affine exterior-power comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01I8 "affine tilde exterior-power comparison inverse law"]
theorem comparison_comp_comparisonInv (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    comparison M n ≫ comparisonInv M n h = 𝟙 _ := sorry

/-- The explicit inverse of the affine exterior-power comparison followed by the comparison is the
identity. -/
@[simp, stacks 01I8 "affine tilde exterior-power comparison inverse law"]
theorem comparisonInv_comp_comparison (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    comparisonInv M n h ≫ comparison M n = 𝟙 _ := sorry

/-- The inverse affine exterior-power comparisons are natural in the module. -/
@[stacks 01I8 "naturality of inverse affine tilde exterior-power comparison"]
theorem comparisonInv_naturality {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ)
    (hM : IsIso (comparison M n)) (hN : IsIso (comparison N n)) :
    RingedSpace.ExteriorPower.map ((tilde.functor R).map f) n ≫ comparisonInv N n hN =
      comparisonInv M n hM ≫
        (tilde.functor R).map (ModuleCat.exteriorPower.map f n) := sorry

/-- Bundle the affine exterior-power comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit affine tilde exterior-power comparison isomorphism"]
noncomputable def comparisonIsoOf (M : ModuleCat R) (n : ℕ)
    (h : IsIso (comparison M n)) :
    tilde (M.exteriorPower n) ≅ (Λ[n] (tilde M) : (Spec R).Modules) :=
  h.toIso

/-- The affine tilde exterior-power comparisons form a natural transformation. -/
@[stacks 01I8 "natural comparison for affine tilde exterior powers"]
noncomputable def comparisonNatTrans (R : CommRingCat.{u}) (n : ℕ) :
    ModuleCat.exteriorPower.functor R n ⋙ tilde.functor R ⟶
      tilde.functor R ⋙ RingedSpace.ExteriorPower.functor (Spec R).toRingedSpace n where
  app M := comparison M n
  naturality := fun {M N} f => ExteriorPower.naturality f n

/-- A component of the affine tilde exterior-power natural transformation is the canonical
comparison. -/
@[simp, stacks 01I8 "component of the affine tilde exterior-power natural comparison"]
theorem comparisonNatTrans_app (M : ModuleCat R) (n : ℕ) :
    (comparisonNatTrans R n).app M = comparison M n := sorry

/-- The affine tilde exterior-power natural comparison is pointwise invertible; its proposition is
available as an explicit certificate for the natural isomorphism bridge. -/
@[stacks 01I8 "invertibility of the affine tilde exterior-power natural comparison"]
theorem comparisonNatTrans_isIso (R : CommRingCat.{u}) (n : ℕ) :
    IsIso (comparisonNatTrans R n) := sorry

/-- Bundle the natural affine exterior-power comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit natural affine tilde exterior-power comparison isomorphism"]
noncomputable def comparisonNatIsoOf (R : CommRingCat.{u}) (n : ℕ)
    (h : IsIso (comparisonNatTrans R n)) :
    ModuleCat.exteriorPower.functor R n ⋙ tilde.functor R ≅
      tilde.functor R ⋙ RingedSpace.ExteriorPower.functor (Spec R).toRingedSpace n :=
  h.toIso

end ExteriorPower

namespace InternalHom

/-- The top-open global section represented by the map induced on affine tilde sheaves. -/
@[stacks 01I8 "affine tilde internal-Hom section comparison"]
noncomputable def adjointFun (M N : ModuleCat R) (f : (ihom M).obj N) :
    moduleSpecΓFunctor.obj ((ihom (tilde M)).obj (tilde N)) :=
  AlgebraicGeometry.RingedSpace.sectionsEquivTop ((ihom (tilde M)).obj (tilde N))
    ((SheafOfModules.RingedSite.InternalHom.sectionsHomEquiv
      (Spec R).sheaf (tilde M) (tilde N)).symm
        ((tilde.functor R).map (f : M ⟶ N)))

/-- Additivity of the affine internal-Hom section comparison. -/
@[stacks 01I8 "additivity of affine tilde internal-Hom sections"]
theorem adjointFun_add (M N : ModuleCat R) (f g : (ihom M).obj N) :
    adjointFun M N (f + g) = adjointFun M N f + adjointFun M N g := sorry

/-- Scalar compatibility of the affine internal-Hom section comparison. -/
@[stacks 01I8 "scalar compatibility of affine tilde internal-Hom sections"]
theorem adjointFun_smul (M N : ModuleCat R) (r : R) (f : (ihom M).obj N) :
    adjointFun M N (r • f) = r • adjointFun M N f := sorry

/-- The affine internal-Hom section map preserves the zero element. -/
@[stacks 01I8 "zero compatibility of affine internal-Hom sections"]
theorem adjointFun_zero (M N : ModuleCat R) :
    adjointFun M N 0 = 0 := sorry

/-- The underlying additive-group morphism of the affine internal-Hom comparison. -/
@[stacks 01I8 "additive affine internal-Hom section comparison"]
noncomputable def adjointAdditive (M N : ModuleCat R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj ((ihom M).obj N) ⟶
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        (moduleSpecΓFunctor.obj ((ihom (tilde M)).obj (tilde N))) :=
  AddCommGrpCat.ofHom
    { toFun := adjointFun M N
      map_zero' := adjointFun_zero M N
      map_add' := adjointFun_add M N }

/-- The additive internal-Hom section map commutes with scalar multiplication. -/
@[stacks 01I8 "scalar compatibility of additive affine internal-Hom sections"]
theorem adjointAdditive_smul (M N : ModuleCat R) (r : R) :
    adjointAdditive M N ≫
        (moduleSpecΓFunctor.obj ((ihom (tilde M)).obj (tilde N))).smul r =
      ((ihom M).obj N).smul r ≫ adjointAdditive M N := sorry

/-- The global-sections morphism adjoint to the affine internal-Hom comparison. -/
@[stacks 01I8 "adjoint affine tilde internal-Hom comparison"]
noncomputable def adjoint (M N : ModuleCat R) :
    (ihom M).obj N ⟶ moduleSpecΓFunctor.obj ((ihom (tilde M)).obj (tilde N)) :=
  ModuleCat.homMk (adjointAdditive M N) (fun r => adjointAdditive_smul M N r)

/-- The canonical comparison from tilde of a module internal Hom to the internal Hom of the
corresponding affine tilde sheaves. -/
@[stacks 01I8 "affine tilde internal-Hom comparison"]
noncomputable def comparison (M N : ModuleCat R) :
    tilde ((ihom M).obj N) ⟶ (ihom (tilde M)).obj (tilde N) :=
  (tilde.adjunction.homEquiv _ _).symm (adjoint M N)

/-- The adjunction transpose recovers the defining affine internal-Hom section map. -/
@[simp, stacks 01I8 "adjunction transpose of affine tilde internal-Hom comparison"]
theorem homEquiv_comparison (M N : ModuleCat R) :
    tilde.adjunction.homEquiv _ _ (comparison M N) = adjoint M N := sorry

/-- The affine tilde internal-Hom comparison is natural in its target module. -/
@[stacks 01I8 "naturality of affine tilde internal-Hom comparison"]
theorem naturality (M : ModuleCat R) {N P : ModuleCat R} (f : N ⟶ P) :
    (tilde.functor R).map ((ihom M).map f) ≫ comparison M P =
      comparison M N ≫ (ihom (tilde M)).map ((tilde.functor R).map f) := sorry

/-- The affine tilde internal-Hom comparison is contravariantly natural in its source module. -/
@[stacks 01I8 "contravariant naturality of affine tilde internal-Hom comparison"]
theorem naturality_left {L M : ModuleCat R} (f : L ⟶ M) (N : ModuleCat R) :
    comparison M N ≫
        (MonoidalClosed.pre ((tilde.functor R).map f)).app (tilde N) =
      (tilde.functor R).map ((MonoidalClosed.pre f).app N) ≫ comparison L N := sorry

/-- For a fixed source module, the affine tilde internal-Hom comparisons form a natural
transformation in the target module. -/
@[stacks 01I8 "affine tilde internal-Hom natural comparison"]
noncomputable def natTrans (M : ModuleCat R) :
    ihom M ⋙ tilde.functor R ⟶ tilde.functor R ⋙ ihom (tilde M) where
  app N := comparison M N
  naturality := fun {N P} f => InternalHom.naturality M f

/-- A component of `natTrans` is the canonical affine tilde internal-Hom comparison. -/
@[simp, stacks 01I8 "component of affine tilde internal-Hom natural comparison"]
theorem natTrans_app (M N : ModuleCat R) :
    (natTrans M).app N = comparison M N := sorry

/-- For a finitely presented source module, the canonical affine tilde internal-Hom comparison is
invertible.  Its proposition is passed explicitly to inverse bridges. -/
@[stacks 01I8 "invertibility of the affine tilde internal-Hom comparison"]
theorem comparisonIsIso (M N : ModuleCat R)
    [Module.FinitePresentation R M] : IsIso (comparison M N) := sorry

/-- The inverse of the affine internal-Hom comparison obtained from its available invertibility
certificate. -/
@[stacks 01I8 "explicit inverse of affine tilde internal-Hom comparison"]
noncomputable def comparisonInv (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    (ihom (tilde M)).obj (tilde N) ⟶ tilde ((ihom M).obj N) :=
  h.toIso.inv

/-- The affine internal-Hom comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01I8 "affine tilde internal-Hom comparison inverse law"]
theorem comparison_comp_comparisonInv (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    comparison M N ≫ comparisonInv M N h = 𝟙 _ := sorry

/-- The explicit inverse of the affine internal-Hom comparison followed by the comparison is the
identity. -/
@[simp, stacks 01I8 "affine tilde internal-Hom comparison inverse law"]
theorem comparisonInv_comp_comparison (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    comparisonInv M N h ≫ comparison M N = 𝟙 _ := sorry

/-- The inverse affine internal-Hom comparisons are natural in the target module. -/
@[stacks 01I8 "naturality of inverse affine tilde internal-Hom comparison"]
theorem comparisonInv_naturality (M : ModuleCat R) {N P : ModuleCat R}
    (f : N ⟶ P) (hN : IsIso (comparison M N)) (hP : IsIso (comparison M P)) :
    (ihom (tilde M)).map ((tilde.functor R).map f) ≫ comparisonInv M P hP =
      comparisonInv M N hN ≫ (tilde.functor R).map ((ihom M).map f) := sorry

/-- The inverse affine internal-Hom comparisons are contravariantly natural in the source
module. -/
@[stacks 01I8 "contravariant naturality of inverse affine tilde internal-Hom comparison"]
theorem comparisonInv_naturality_left {L M : ModuleCat R} (f : L ⟶ M) (N : ModuleCat R)
    (hL : IsIso (comparison L N)) (hM : IsIso (comparison M N)) :
    (MonoidalClosed.pre ((tilde.functor R).map f)).app (tilde N) ≫ comparisonInv L N hL =
      comparisonInv M N hM ≫ (tilde.functor R).map ((MonoidalClosed.pre f).app N) := sorry

/-- Bundle the affine internal-Hom comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit affine tilde internal-Hom comparison isomorphism"]
noncomputable def comparisonIsoOf (M N : ModuleCat R)
    (h : IsIso (comparison M N)) :
    tilde ((ihom M).obj N) ≅ (ihom (tilde M)).obj (tilde N) :=
  h.toIso

/-- Finite presentation of the source makes the target-variable affine tilde comparison
invertible; its proposition is available as an explicit certificate. -/
@[stacks 01I8 "invertibility of the affine tilde internal-Hom natural transformation"]
theorem natTrans_isIso (M : ModuleCat R)
    [Module.FinitePresentation R M] : IsIso (natTrans M) := sorry

/-- Bundle the natural affine internal-Hom comparison with its available invertibility certificate. -/
@[stacks 01I8 "explicit natural affine tilde internal-Hom comparison isomorphism"]
noncomputable def natIsoOf (M : ModuleCat R)
    (h : IsIso (natTrans M)) :
    ihom M ⋙ tilde.functor R ≅ tilde.functor R ⋙ ihom (tilde M) :=
  h.toIso

end InternalHom

end AlgebraicGeometry.tilde
