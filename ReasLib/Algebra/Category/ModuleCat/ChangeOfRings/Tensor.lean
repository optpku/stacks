/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.RingTheory.Algebra.TensorProduct.Finite
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Tensor models for extension of scalars

This leaf supplies the canonical identification of `ModuleCat.extendScalars`
with the usual tensor-product module, together with the finiteness and
freeness instances transported through that identification.  It deliberately
keeps the two scalar structures on the first tensor factor local: making the
right-algebra structure global creates competing canonical instances.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open Functor.OplaxMonoidal
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

noncomputable section

namespace ModuleCat.ExtendScalars

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

-- Local instance justification (instance diamond): tensor normalization needs this orientation,
-- while exporting it would create competing scalar-action paths throughout `ModuleCat`.
attribute [local instance] SMulCommClass.of_commMonoid

/-- The restricted scalar module `S`, viewed again as an `S`-module, is
canonically linearly equivalent to `S`. -/
noncomputable def restrictSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
  { __ := AddEquiv.refl S
    map_smul' := fun _ _ ↦ rfl }

/-- The categorical extension of scalars along `R → S` is the standard
tensor-product `S ⊗[R] M`. -/
@[stacks 08JZ "scalar-extension tensor normalization"]
noncomputable def tensorIso (M : ModuleCat.{w} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictSelfEquiv (R := R) (S := S))
      (LinearEquiv.refl R M)).toModuleIso

/-- The tensor normalization of extension of scalars is natural in the module. -/
@[reassoc, stacks 08JZ "scalar-extension tensor naturality"]
theorem tensorIso_naturality {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R S)).map f ≫
        (tensorIso (R := R) (S := S) N).hom =
      (tensorIso (R := R) (S := S) M).hom ≫
        ModuleCat.ofHom (f.hom.baseChange S) := by
  rw [← cancel_epi (tensorIso (R := R) (S := S) M).inv]
  simp only [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Tensoring the zero `R`-module with `S` gives the zero `S`-module. -/
@[stacks 08JZ "scalar-extension tensor normalization"]
noncomputable def tensorPUnitIso :
    ModuleCat.of S (S ⊗[R] PUnit) ≅ ModuleCat.of S PUnit :=
  (LinearEquiv.ofSubsingleton _ _).toModuleIso

/-- The monoidal comparison for extension of scalars is natural in the right
tensor factor. -/
@[stacks 00M8 "extension-of-scalars tensor comparison"]
theorem tensorLeftIso_naturality
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) {X Y : ModuleCat R} (g : X ⟶ Y) :
    (tensorLeft M ⋙ ModuleCat.extendScalars f).map g ≫
        (Functor.Monoidal.μIso (ModuleCat.extendScalars f) M Y).symm.hom =
      (Functor.Monoidal.μIso (ModuleCat.extendScalars f) M X).symm.hom ≫
        (ModuleCat.extendScalars f ⋙
          tensorLeft ((ModuleCat.extendScalars f).obj M)).map g := by
  change
    (ModuleCat.extendScalars f).map (M ◁ g) ≫
        Functor.OplaxMonoidal.δ (ModuleCat.extendScalars f) M Y =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars f) M X ≫
        (ModuleCat.extendScalars f).obj M ◁ (ModuleCat.extendScalars f).map g
  exact (Functor.OplaxMonoidal.δ_natural_right (ModuleCat.extendScalars f) M g).symm

/-- Extension of scalars commutes canonically with tensoring on the left by a
fixed module. -/
@[stacks 00M8 "extension-of-scalars tensor comparison"]
noncomputable def tensorLeftIso
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) :
    tensorLeft M ⋙ ModuleCat.extendScalars f ≅
      ModuleCat.extendScalars f ⋙ tensorLeft ((ModuleCat.extendScalars f).obj M) :=
  NatIso.ofComponents
    (fun X ↦ (Functor.Monoidal.μIso (ModuleCat.extendScalars f) M X).symm)
    (tensorLeftIso_naturality f M)

section Finiteness

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Extension of scalars preserves finite generation of modules, independently of the chosen
homological or presentation model. -/
@[stacks 08JZ "scalar-extension finite modules"]
instance (priority := 100) finite
    (f : R →+* S) (M : ModuleCat.{w} R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.extendScalars.{u, v, w} f).obj M) := by
  -- Local instance justification (defeq pin): extension of scalars is indexed by this homomorphism.
  letI := f.toAlgebra
  change Module.Finite S (S ⊗[R] M)
  infer_instance

/-- Extension of scalars preserves free modules, independently of the chosen homological or
presentation model. -/
@[stacks 08JZ "scalar-extension free modules"]
instance (priority := 100) free
    (f : R →+* S) (M : ModuleCat.{w} R) [Module.Free R M] :
    Module.Free S ((ModuleCat.extendScalars.{u, v, w} f).obj M) := by
  -- Local instance justification (defeq pin): extension of scalars is indexed by this homomorphism.
  letI := f.toAlgebra
  change Module.Free S (S ⊗[R] M)
  infer_instance

end Finiteness

section Restrict

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- After forgetting the extended `S`-action, categorical extension of scalars is canonically
tensoring on the left by the underlying `R`-module `S`. -/
@[stacks 09PQ "restricted scalar extension as tensoring on the left"]
noncomputable def restrictTensorIso (M : ModuleCat R) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≅
      (tensorLeft (ModuleCat.of R S)).obj M :=
  (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      (tensorIso (R := R) (S := S) M) ≪≫
    ModuleCat.RestrictScalars.identityIso (R := R) (S := S) (S ⊗[R] M)

/-- The restricted scalar-extension comparison is the identity on pure tensors. -/
@[simp]
theorem restrictTensorIso_hom_tmul (M : ModuleCat R) (s : S) (m : M) :
    (restrictTensorIso (R := R) (S := S) M).hom (s ⊗ₜ[R] m) = s ⊗ₜ[R] m := by
  rfl

/-- On pure tensors, the inverse restricted comparison is the inverse tensor normalization. -/
@[simp]
theorem restrictTensorIso_inv_tmul (M : ModuleCat R) (s : S) (m : M) :
    (restrictTensorIso (R := R) (S := S) M).inv (s ⊗ₜ[R] m) =
      (tensorIso (R := R) (S := S) M).inv (s ⊗ₜ[R] m) := by
  rfl

/-- The restricted scalar-extension comparison is natural in the module. -/
theorem restrictTensorIso_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    (ModuleCat.restrictScalars (algebraMap R S)).map
          ((ModuleCat.extendScalars (algebraMap R S)).map f) ≫
        (restrictTensorIso (R := R) (S := S) N).hom =
      (restrictTensorIso (R := R) (S := S) M).hom ≫
        (tensorLeft (ModuleCat.of R S)).map f := by
  rw [← cancel_epi (restrictTensorIso (R := R) (S := S) M).inv]
  simp only [Iso.inv_hom_id_assoc]
  let α :=
    (restrictTensorIso (R := R) (S := S) M).inv ≫
      (ModuleCat.restrictScalars (algebraMap R S)).map
        ((ModuleCat.extendScalars (algebraMap R S)).map f) ≫
      (restrictTensorIso (R := R) (S := S) N).hom
  let β := (tensorLeft (ModuleCat.of R S)).map f
  change α = β
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul s m => rfl
  | add x y hx hy =>
      exact (α.hom.map_add x y).trans <|
        (congrArg₂ (fun a b ↦ a + b) hx hy).trans (β.hom.map_add x y).symm

/-- Restriction after extension of scalars is naturally isomorphic to tensoring on the left by
the scalar algebra, regarded as a module over the source ring. -/
@[stacks 09PQ "restricted extension-of-scalars tensor comparison"]
noncomputable def restrictTensorNatIso :
    ModuleCat.extendScalars (algebraMap R S) ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      tensorLeft (ModuleCat.of R S) :=
  NatIso.ofComponents
    (restrictTensorIso (R := R) (S := S))
    (fun f ↦ restrictTensorIso_naturality (R := R) (S := S) f)

end Restrict

end ModuleCat.ExtendScalars
