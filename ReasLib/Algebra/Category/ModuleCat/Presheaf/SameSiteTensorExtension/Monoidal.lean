module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-!
# Tensor comparison for sectionwise extension of scalars

The comparison on every section is the usual base-change tensor isomorphism.
Both directions use Mathlib's explicit scalar-extension maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe c v w

namespace PresheafOfModules.SameSiteTensorExtension

variable {C : Type c} [Category.{v} C]
variable {R S : Cᵒᵖ ⥤ CommRingCat.{w}} (α : R ⟶ S)

local instance sourceMonoidal :
    MonoidalCategory (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.monoidalCategory (R := R)

local instance targetMonoidal :
    MonoidalCategory (PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.monoidalCategory (R := S)

/-- Base change sends the tensor of the two sectionwise extensions to the
extension of the original tensor. -/
def tensorHom (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    (functor α).obj M ⊗ (functor α).obj N ⟶ (functor α).obj (M ⊗ N) where
  app U := Functor.LaxMonoidal.μ (ModuleCat.extendScalars (α.app U).hom) (M.obj U) (N.obj U)
  naturality := sorry

/-- The reverse comparison distributes a sectionwise scalar extension over
the original tensor product. -/
def tensorInv (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    (functor α).obj (M ⊗ N) ⟶ (functor α).obj M ⊗ (functor α).obj N where
  app U := Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (α.app U).hom) (M.obj U) (N.obj U)
  naturality := sorry

/-- Extension of scalars commutes with pointwise tensor products by the
specified base-change maps in both directions. -/
def tensorIso (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    (functor α).obj M ⊗ (functor α).obj N ≅ (functor α).obj (M ⊗ N) where
  hom := tensorHom α M N
  inv := tensorInv α M N
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit map on sections sends `s` to `s ⊗ 1` through the canonical
scalar-extension unit isomorphism. -/
def unitHom :
    𝟙_ (PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) ⟶
      (functor α).obj (𝟙_ (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))) where
  app U := Functor.LaxMonoidal.ε (ModuleCat.extendScalars (α.app U).hom)
  naturality := sorry

/-- The reverse unit map is the sectionwise scalar-extension multiplication. -/
def unitInv :
    (functor α).obj (𝟙_ (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))) ⟶
      𝟙_ (PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) where
  app U := Functor.OplaxMonoidal.η (ModuleCat.extendScalars (α.app U).hom)
  naturality := sorry

/-- The sectionwise unit comparison with both actual component maps. -/
def unitIso :
    𝟙_ (PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) ≅
      (functor α).obj (𝟙_ (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))) where
  hom := unitHom α
  inv := unitInv α
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The sectionwise tensor and unit maps form a strong monoidal core. -/
def coreMonoidal : (functor α).CoreMonoidal :=
  Functor.CoreMonoidal.mk'
    (εIso := unitIso α)
    (μIso := tensorIso α)
    (μIso_inv_natural_left := sorry)
    (μIso_inv_natural_right := sorry)
    (oplax_associativity := sorry)
    (oplax_left_unitality := sorry)
    (oplax_right_unitality := sorry)

/-- The tensor comparison is the native scalar-extension tensor map at every
object of the indexing category. -/
@[simp]
theorem tensorHom_app (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) :
    (tensorHom α M N).app U =
      Functor.LaxMonoidal.μ (ModuleCat.extendScalars (α.app U).hom) (M.obj U) (N.obj U) := rfl

/-- The inverse tensor comparison is the native reverse base-change map. -/
@[simp]
theorem tensorInv_app (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) :
    (tensorInv α M N).app U =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (α.app U).hom) (M.obj U) (N.obj U) := rfl

/-- On pure tensors the forward map multiplies the two extended coefficients. -/
@[simp]
theorem tensorHom_tmul (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (m : M.obj U) (n : N.obj U) (a b : S.obj U) :
    letI := (α.app U).hom.toAlgebra
    ((tensorHom α M N).app U).hom
        ((a ⊗ₜ[R.obj U] m) ⊗ₜ[S.obj U] (b ⊗ₜ[R.obj U] n)) =
      (a * b) ⊗ₜ[R.obj U] (m ⊗ₜ[R.obj U] n) := by
  letI := (α.app U).hom.toAlgebra
  change (TensorProduct.AlgebraTensorModule.distribBaseChange
    (R.obj U) (S.obj U) (M.obj U) (N.obj U)).symm _ = _
  exact TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul _ _ m n a b

/-- On a generator the reverse map distributes the scalar extension to both factors. -/
@[simp]
theorem tensorInv_one_tmul (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (m : M.obj U) (n : N.obj U) :
    letI := (α.app U).hom.toAlgebra
    ((tensorInv α M N).app U).hom ((1 : S.obj U) ⊗ₜ[R.obj U] (m ⊗ₜ[R.obj U] n)) =
      ((1 : S.obj U) ⊗ₜ[R.obj U] m) ⊗ₜ[S.obj U] ((1 : S.obj U) ⊗ₜ[R.obj U] n) := rfl

end PresheafOfModules.SameSiteTensorExtension
