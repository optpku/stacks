/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Localization
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.DifferentialOperator
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Differential operators on affine schemes

Taking sections on the top open of an affine scheme sends relative differential operators
between module sheaves to differential operators between their modules of global sections.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.AffineDifferentialOperator

variable {R A : CommRingCat.{u}}

/-- The restricted-scalar morphism on affine global sections induced by a relative differential
operator between module sheaves. -/
noncomputable def globalSectionsHom (φ : R ⟶ A) {ℱ 𝒢 : (Spec A).Modules} {k : ℕ}
    (D : Diff((Spec.map φ).toShHom ; k ; ℱ, 𝒢)) :
    (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := A)).obj ℱ) ⟶
      (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := A)).obj 𝒢) :=
  let source :=
    (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := A)).obj ℱ)
  let target :=
    (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := A)).obj 𝒢)
  @ModuleCat.ofHom R _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun m ↦
        ((SheafOfModules.RingedSite.DifferentialOperators.toHom D).val.app
          (op (⊤ : (Spec A).Opens))).hom m
      map_add' := fun x y ↦
        ((SheafOfModules.RingedSite.DifferentialOperators.toHom D).val.app
          (op (⊤ : (Spec A).Opens))).hom.map_add x y
      map_smul' := sorry }

/-- The morphism on affine global sections induced by an order-`k` sheaf differential operator
has differential-operator order at most `k`. -/
theorem globalSectionsHom_isOfOrder (φ : R ⟶ A) {ℱ 𝒢 : (Spec A).Modules} {k : ℕ}
    (D : Diff((Spec.map φ).toShHom ; k ; ℱ, 𝒢)) :
    ModuleCat.IsDifferentialOperatorOfOrder φ.hom (globalSectionsHom φ D) k := sorry

/-- Taking affine global sections sends a relative order-`k` differential operator between
module sheaves to an order-`k` differential operator between their global-sections modules. -/
noncomputable def globalSections (φ : R ⟶ A) (ℱ 𝒢 : (Spec A).Modules) (k : ℕ) :
    Diff((Spec.map φ).toShHom ; k ; ℱ, 𝒢) →
      ModuleCat.DifferentialOperators.ofOrder φ.hom
        ((moduleSpecΓFunctor (R := A)).obj ℱ) k
        ((moduleSpecΓFunctor (R := A)).obj 𝒢) :=
  fun D ↦ ModuleCat.DifferentialOperators.ofHom (globalSectionsHom φ D)
    (globalSectionsHom_isOfOrder φ D)

/-- On an affine global section, `globalSections` applies the top-open component of the sheaf
differential operator. -/
@[simp]
theorem globalSections_apply (φ : R ⟶ A) (ℱ 𝒢 : (Spec A).Modules) (k : ℕ)
    (D : Diff((Spec.map φ).toShHom ; k ; ℱ, 𝒢))
    (m : (moduleSpecΓFunctor (R := A)).obj ℱ) :
    (ModuleCat.DifferentialOperators.toHom (globalSections φ ℱ 𝒢 k D)).hom m =
      ((SheafOfModules.RingedSite.DifferentialOperators.toHom D).val.app
        (op (⊤ : (Spec A).Opens))).hom m := rfl

/-- If the source module sheaf on an affine scheme is quasicoherent, taking global sections is a
bijection on relative differential operators of every fixed finite order. -/
theorem globalSections_bijective (φ : R ⟶ A) (ℱ 𝒢 : (Spec A).Modules)
    [ℱ.IsQuasicoherent] (k : ℕ) :
    Function.Bijective (globalSections φ ℱ 𝒢 k) := sorry

end AlgebraicGeometry.Scheme.Modules.AffineDifferentialOperator
