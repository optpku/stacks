/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe c v u

namespace SheafOfModules.TensorScalarExtension
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

/-- A commutative view of the same ring operations; only the commutativity law is added. -/
def commView (R : Cᵒᵖ ⥤ RingCat.{u})
    (hR : ∀ U (x y : R.obj U), x * y = y * x) : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := @CommRingCat.of (R.obj U) { (inferInstance : Ring (R.obj U)) with mul_comm := hR U }
  map {U V} f := @CommRingCat.ofHom
    (R.obj U) (R.obj V)
    { (inferInstance : Ring (R.obj U)) with mul_comm := hR U }
    { (inferInstance : Ring (R.obj V)) with mul_comm := hR V } (R.map f).hom
  map_id U := by apply CommRingCat.hom_ext; exact congrArg RingCat.Hom.hom (R.map_id U)
  map_comp f g := by apply CommRingCat.hom_ext; exact congrArg RingCat.Hom.hom (R.map_comp f g)

/-- Forgetting the commutative view recovers precisely the original ring presheaf. -/
theorem commView_forget (R : Cᵒᵖ ⥤ RingCat.{u})
    (hR : ∀ U (x y : R.obj U), x * y = y * x) :
    commView R hR ⋙ forget₂ CommRingCat RingCat = R := rfl

/-- The original ring map between the commutative views. -/
def commMap {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
    (hR : ∀ U (x y : R.obj U), x * y = y * x)
    (hR' : ∀ U (x y : R'.obj U), x * y = y * x) :
    commView R hR ⟶ commView R' hR' where
  app U := @CommRingCat.ofHom (R.obj U) (R'.obj U)
    { (inferInstance : Ring (R.obj U)) with mul_comm := hR U }
    { (inferInstance : Ring (R'.obj U)) with mul_comm := hR' U } (α.app U).hom
  naturality _ _ f := by
    apply CommRingCat.hom_ext
    exact congrArg RingCat.Hom.hom (α.naturality f)

variable {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
variable (hR : ∀ U (x y : R.obj.obj U), x * y = y * x)
variable (hR' : ∀ U (x y : R'.obj.obj U), x * y = y * x)
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The identity coefficient morphism is locally injective. -/
instance identityLocallyInjective : Presheaf.IsLocallyInjective J (𝟙 R'.obj) :=
  Presheaf.isLocallyInjective_of_injective J (𝟙 R'.obj) (fun _ ↦ Function.injective_id)

/-- The identity coefficient morphism is locally surjective. -/
instance identityLocallySurjective : Presheaf.IsLocallySurjective J (𝟙 R'.obj) :=
  Presheaf.isLocallySurjective_of_surjective J (𝟙 R'.obj) (fun _ ↦ Function.surjective_id)

/-- Extension uses sectionwise tensors followed by module sheafification. -/
def functor : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R' :=
  SheafOfModules.forget R ⋙
    PresheafOfModules.SameSiteTensorExtension.functor (commMap α.hom hR hR') ⋙
    PresheafOfModules.sheafification (R₀ := R'.obj) (R := R') (𝟙 R'.obj)

/-- The Hom equivalence consists of the actual sheafification and tensor Hom maps. -/
def homEquiv (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} R') :
    ((functor α hR hR').obj M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars α).obj N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R'.obj)).homEquiv _ _).trans
    (((PresheafOfModules.SameSiteTensorExtension.adjunction
        (commMap α.hom hR hR')).homEquiv M.val N.val).trans
      ((SheafOfModules.fullyFaithfulForget R).homEquiv
        (X := M) (Y := (SheafOfModules.restrictScalars α).obj N)).symm)

/-- The scalar adjunction has concrete tensor/sheafification Hom maps. -/
def adjunction : functor α hR hR' ⊣ SheafOfModules.restrictScalars α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv α hR hR'
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

end SheafOfModules.TensorScalarExtension
