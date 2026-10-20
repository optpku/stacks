/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout.Comparison
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Tensor-ring actions on derived base-change cohomology -/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedBaseChange

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- Cohomology of restriction to the base ring followed by derived scalar extension. -/
def homology (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) : ModuleCat.{u} R' :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
    ((Pushout.DerivedExtension.baseDerived (R := R) (R' := R')).obj K)

/-- The endomorphism on base-change cohomology induced by a source scalar. -/
def scalar (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (a : A) :
    Module.End R' (homology (R := R) (R' := R') K i) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).map
    ((Pushout.DerivedExtension.baseDerived (R := R) (R' := R')).map (a • 𝟙 K))).hom

/-- The unit of the source ring acts as the identity on base-change cohomology. -/
theorem scalar_one (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    scalar (R := R) (R' := R') K i 1 = 1 := sorry

/-- Multiplication of source scalars acts by composition on base-change cohomology. -/
theorem scalar_mul (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (a b : A) :
    scalar (R := R) (R' := R') K i (a * b) =
      scalar (R := R) (R' := R') K i a * scalar (R := R) (R' := R') K i b := sorry

/-- The zero source scalar acts by zero on base-change cohomology. -/
theorem scalar_zero (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    scalar (R := R) (R' := R') K i 0 = 0 := sorry

/-- Addition of source scalars acts additively on base-change cohomology. -/
theorem scalar_add (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (a b : A) :
    scalar (R := R) (R' := R') K i (a + b) =
      scalar (R := R) (R' := R') K i a + scalar (R := R) (R' := R') K i b := sorry

/-- A base scalar acts through its image in the changed-base ring. -/
theorem scalar_base (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (r : R) :
    scalar (R := R) (R' := R') K i (algebraMap R A r) =
      algebraMap R' (Module.End R' (homology (R := R) (R' := R') K i))
        (algebraMap R R' r) := sorry

/-- The source-ring representation on base-change cohomology. -/
def scalarAction (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    A →+* Module.End R' (homology (R := R) (R' := R') K i) where
  toFun := scalar K i
  map_one' := scalar_one K i
  map_mul' := scalar_mul K i
  map_zero' := scalar_zero K i
  map_add' := scalar_add K i

/-- The commuting source and changed-base actions induce a tensor-ring representation. -/
def tensorAction (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    (A ⊗[R] R') →+* Module.End R' (homology (R := R) (R' := R') K i) :=
  -- Local instance justification (noncanonical choice): restrict the canonical central
  -- endomorphism algebra along the fixed base-change algebra map.
  let _ := Algebra.compHom (Module.End R' (homology (R := R) (R' := R') K i))
    (algebraMap R R')
  let left : A →ₐ[R] Module.End R' (homology (R := R) (R' := R') K i) :=
    { scalarAction K i with commutes' := scalar_base K i }
  let right : R' →ₐ[R] Module.End R' (homology (R := R) (R' := R') K i) :=
    { toRingHom := algebraMap R' _
      commutes' := fun _ ↦ rfl }
  -- Local instance justification (instance diamond): use the self-scalar tower belonging
  -- to the displayed restricted endomorphism algebra.
  let _ : IsScalarTower R R (Module.End R' (homology (R := R) (R' := R') K i)) :=
    IsScalarTower.left R
  (Algebra.TensorProduct.lift left right
    (fun a b ↦ Algebra.commute_algebraMap_right b (left a))).toRingHom

/-- Base-change cohomology with its canonical tensor-product coefficient-ring action. -/
def homologyModule (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    ModuleCat.{u} (A ⊗[R] R') :=
  @ModuleCat.of (A ⊗[R] R') _ (homology (R := R) (R' := R') K i) _
    (Module.compHom _ (tensorAction K i))

/-- A pure tensor acts by its source scalar and its changed-base scalar. -/
theorem homologyModule_tmul (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    (a : A) (b : R') (m : homologyModule (R := R) (R' := R') K i) :
    (a ⊗ₜ[R] b) • m = b • scalar (R := R) (R' := R') K i a m := sorry

variable {A' : Type u} [CommRing A']

/-- The canonical comparison from base derived extension to restriction of source derived
extension, obtained by transposing the derived adjunction unit. -/
def comparison (σ : (A ⊗[R] R') →+* A') (ρ : A →+* A')
    (hleft : σ.comp Algebra.TensorProduct.includeLeftRingHom = ρ)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (Pushout.DerivedExtension.baseDerived (R := R) (R' := R')).obj K ⟶
      (derivedRestrictionOfScalars (σ.comp Algebra.TensorProduct.includeRight.toRingHom)).obj
        ((derivedExtensionOfScalars ρ).obj K) :=
  let τ := σ.comp Algebra.TensorProduct.includeRight.toRingHom
  let L := (derivedExtensionOfScalars ρ).obj K
  let hbase : ρ.comp (algebraMap R A) = τ.comp (algebraMap R R') :=
    (congrArg (fun t : A →+* A' ↦ t.comp (algebraMap R A)) hleft).symm.trans
      ((RingHom.comp_assoc _ _ _).trans
        ((congrArg (fun t ↦ σ.comp t)
          Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap).trans
            (RingHom.comp_assoc _ _ _).symm))
  ((derivedExtensionRestrictionAdjunction (algebraMap R R')).homEquiv _ _).symm
    ((derivedRestrictionOfScalars (algebraMap R A)).map
        ((derivedExtensionRestrictionAdjunction ρ).unit.app K) ≫
      (DerivedRestriction.compObjIso (algebraMap R A) ρ L).inv ≫
      (DerivedRestriction.compObjIsoOfEq (algebraMap R R') τ
        (ρ.comp (algebraMap R A)) hbase L).hom)

/-- The changed-base-linear map on cohomology induced by the canonical comparison and a
map out of source derived extension. -/
def homologyMap (σ : (A ⊗[R] R') →+* A') (ρ : A →+* A')
    (hleft : σ.comp Algebra.TensorProduct.includeLeftRingHom = ρ)
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (α : (derivedExtensionOfScalars ρ).obj K ⟶ K') (i : ℤ) :
    homology (R := R) (R' := R') K i ⟶
      (ModuleCat.restrictScalars (σ.comp Algebra.TensorProduct.includeRight.toRingHom)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj K') :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).map
      (comparison σ ρ hleft K ≫
        (derivedRestrictionOfScalars (σ.comp Algebra.TensorProduct.includeRight.toRingHom)).map α) ≫
    (derivedRestrictionHomologyIso (σ.comp Algebra.TensorProduct.includeRight.toRingHom) K' i).hom

/-- The cohomology comparison intertwines the source-ring action with the target action. -/
theorem homologyMap_smul (σ : (A ⊗[R] R') →+* A') (ρ : A →+* A')
    (hleft : σ.comp Algebra.TensorProduct.includeLeftRingHom = ρ)
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (α : (derivedExtensionOfScalars ρ).obj K ⟶ K') (i : ℤ) (a : A)
    (m : homology (R := R) (R' := R') K i) :
    homologyMap σ ρ hleft K K' α i (scalar (R := R) (R' := R') K i a m) =
      ρ a • homologyMap σ ρ hleft K K' α i m := sorry

/-- The cohomology comparison is linear over the tensor-product coefficient ring. -/
theorem homologyMap_tensor_smul (σ : (A ⊗[R] R') →+* A') (ρ : A →+* A')
    (hleft : σ.comp Algebra.TensorProduct.includeLeftRingHom = ρ)
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (α : (derivedExtensionOfScalars ρ).obj K ⟶ K') (i : ℤ) (t : A ⊗[R] R')
    (m : homologyModule (R := R) (R' := R') K i) :
    homologyMap σ ρ hleft K K' α i (t • m) =
      σ t • homologyMap σ ρ hleft K K' α i m := sorry

/-- The canonical cohomology comparison bundled as a tensor-ring-linear map. -/
def tensorHomologyMap (σ : (A ⊗[R] R') →+* A') (ρ : A →+* A')
    (hleft : σ.comp Algebra.TensorProduct.includeLeftRingHom = ρ)
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (α : (derivedExtensionOfScalars ρ).obj K ⟶ K') (i : ℤ) :
    homologyModule (R := R) (R' := R') K i ⟶
      (ModuleCat.restrictScalars σ).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj K') :=
  (ModuleCat.homEquiv.symm
    { toFun := fun m : homologyModule (R := R) (R' := R') K i ↦
        homologyMap σ ρ hleft K K' α i m
      map_add' := (homologyMap σ ρ hleft K K' α i).hom.map_add
      map_smul' := homologyMap_tensor_smul σ ρ hleft K K' α i } :
    homologyModule (R := R) (R' := R') K i ⟶
      (ModuleCat.restrictScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj K'))

/-- Extending base-change cohomology to the target ring gives its canonical cohomology map. -/
def cohomologyMap (σ : (A ⊗[R] R') →+* A') (ρ : A →+* A')
    (hleft : σ.comp Algebra.TensorProduct.includeLeftRingHom = ρ)
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (α : (derivedExtensionOfScalars ρ).obj K ⟶ K') (i : ℤ) :
    (ModuleCat.extendScalars σ).obj (homologyModule (R := R) (R' := R') K i) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj K' :=
  ((ModuleCat.extendRestrictScalarsAdj σ).homEquiv _ _).symm
    (tensorHomologyMap σ ρ hleft K K' α i)

/-- On a pure tensor, the cohomology map multiplies the cohomology comparison by the
specified target scalar. -/
theorem cohomologyMap_tmul (σ : (A ⊗[R] R') →+* A') (ρ : A →+* A')
    (hleft : σ.comp Algebra.TensorProduct.includeLeftRingHom = ρ)
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (α : (derivedExtensionOfScalars ρ).obj K ⟶ K') (i : ℤ) (a' : A')
    (m : homologyModule (R := R) (R' := R') K i) :
    cohomologyMap σ ρ hleft K K' α i
        (-- Local instance justification (noncanonical choice): the specified target ring map
         -- determines the scalar action in this pure tensor.
         let _ := σ.toAlgebra
         a' ⊗ₜ[A ⊗[R] R'] m) =
      a' • homologyMap σ ρ hleft K K' α i m := sorry

end CategoryTheory.ModuleCat.DerivedBaseChange

end
