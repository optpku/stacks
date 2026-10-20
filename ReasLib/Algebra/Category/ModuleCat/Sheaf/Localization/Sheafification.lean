module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheafification and restriction to a slice site

For an arbitrary sheaf of rings, restriction to a slice site commutes with sheafification of
module presheaves.  The non-Prop comparison data comes from Mathlib's compatibility between
continuous pushforward and additive sheafification.  Scalar compatibility and naturality are
isolated as theorem fields.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Localization.ModuleSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{w}) (U : C)
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{z}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [UnivLE.{max u v, z}]

/-- The additive-sheaf isomorphism underlying compatibility of module sheafification with
restriction to `C / U`, oriented from ambient sheafification to slice sheafification. -/
noncomputable def overAddIso (P : PresheafOfModules.{z} R.obj) :
    (SheafOfModules.toSheaf (R.over U)).obj
        (((PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj P).over U) ≅
      (SheafOfModules.toSheaf (R.over U)).obj
        ((PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).obj (P.over U)) :=
  (((Over.forget U).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{z} (J.over U) J).app P.presheaf).symm

/-- The component of `overAddIso` at an object of the slice site. -/
noncomputable def overAddAppIso
    (P : PresheafOfModules.{z} R.obj) (X : (Over U)ᵒᵖ) :
    (forget₂ (ModuleCat ((R.over U).obj.obj X)) Ab).obj
        ((((PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj P).over U).val.obj X) ≅
      (forget₂ (ModuleCat ((R.over U).obj.obj X)) Ab).obj
        (((PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).obj (P.over U)).val.obj X) :=
  ((CategoryTheory.evaluation (Over U)ᵒᵖ AddCommGrpCat.{z}).obj X).mapIso
    ((sheafToPresheaf (J.over U) AddCommGrpCat.{z}).mapIso (overAddIso R U P))

/-- The additive comparison component respects the scalar action on the restricted ring
sheaf. -/
theorem overAddAppIso_smul
    (P : PresheafOfModules.{z} R.obj) (X : (Over U)ᵒᵖ)
    (r : (R.over U).obj.obj X) :
    (overAddAppIso R U P X).hom ≫
        (((PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).obj (P.over U)).val.obj X).smul r =
      ((((PresheafOfModules.sheafification
          (R₀ := R.obj) (𝟙 R.obj)).obj P).over U).val.obj X).smul r ≫
        (overAddAppIso R U P X).hom := sorry

/-- The module isomorphism underlying localized sheafification at one object of the slice. -/
noncomputable def overAppIso
    (P : PresheafOfModules.{z} R.obj) (X : (Over U)ᵒᵖ) :
    (((PresheafOfModules.sheafification
        (R₀ := R.obj) (𝟙 R.obj)).obj P).over U).val.obj X ≅
      ((PresheafOfModules.sheafification
        (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).obj (P.over U)).val.obj X :=
  ModuleCat.isoMk (overAddAppIso R U P X) (overAddAppIso_smul R U P X)

/-- The pointwise localized-sheafification isomorphisms commute with restriction maps. -/
theorem overAppIso_naturality
    (P : PresheafOfModules.{z} R.obj) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (((PresheafOfModules.sheafification
          (R₀ := R.obj) (𝟙 R.obj)).obj P).over U).val.map f ≫
        (ModuleCat.restrictScalars ((R.over U).obj.map f).hom).map
          (overAppIso R U P Y).hom =
      (overAppIso R U P X).hom ≫
        ((PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).obj (P.over U)).val.map f := sorry

/-- The underlying module presheaves of the ambient and slice sheafifications are canonically
isomorphic. -/
noncomputable def overPresheafIso (P : PresheafOfModules.{z} R.obj) :
    (((PresheafOfModules.sheafification
        (R₀ := R.obj) (𝟙 R.obj)).obj P).over U).val ≅
      ((PresheafOfModules.sheafification
        (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).obj (P.over U)).val :=
  PresheafOfModules.isoMk (overAppIso R U P)
    (fun _ _ f ↦ overAppIso_naturality R U P f)

/-- Module sheafification over an arbitrary sheaf of rings commutes with restriction to a
slice site. -/
@[stacks 04IX "module sheafification commutes with slice restriction"]
noncomputable def overIso (P : PresheafOfModules.{z} R.obj) :
    ((PresheafOfModules.sheafification
        (R₀ := R.obj) (𝟙 R.obj)).obj P).over U ≅
      (PresheafOfModules.sheafification
        (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).obj (P.over U) :=
  (SheafOfModules.fullyFaithfulForget (R.over U)).preimageIso
    (overPresheafIso R U P)

/-- The module-sheafification comparison is natural in the module presheaf. -/
@[stacks 04IX "module-sheafification slice comparison naturality"]
theorem overIso_naturality
    {P Q : PresheafOfModules.{z} R.obj} (f : P ⟶ Q) :
    (SheafOfModules.overFunctor R U).map
          ((PresheafOfModules.sheafification
            (R₀ := R.obj) (𝟙 R.obj)).map f) ≫ (overIso R U Q).hom =
      (overIso R U P).hom ≫
        (PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).map (f.over U) := sorry

/-- The inverse module-sheafification comparison is natural in the module presheaf. -/
@[stacks 04IX "inverse naturality of the module-sheafification slice comparison"]
theorem overIso_inv_naturality
    {P Q : PresheafOfModules.{z} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification
      (R₀ := (R.over U).obj) (𝟙 (R.over U).obj)).map (f.over U) ≫
        (overIso R U Q).inv =
      (overIso R U P).inv ≫
        (SheafOfModules.overFunctor R U).map
          ((PresheafOfModules.sheafification
            (R₀ := R.obj) (𝟙 R.obj)).map f) := sorry

/-- The forward module-sheafification comparisons form a natural transformation. -/
@[stacks 04IX "forward module-sheafification slice comparison natural transformation"]
noncomputable def overNatTrans :
    PresheafOfModules.sheafification
          (R₀ := R.obj) (𝟙 R.obj) ⋙ SheafOfModules.overFunctor R U ⟶
      PresheafOfModules.overFunctor R.obj U ⋙
        PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj) where
  app P := (overIso R U P).hom
  naturality _ _ f := overIso_naturality R U f

/-- The inverse module-sheafification comparisons form the inverse natural transformation. -/
@[stacks 04IX "inverse module-sheafification slice comparison natural transformation"]
noncomputable def overInvNatTrans :
    PresheafOfModules.overFunctor R.obj U ⋙
        PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj) ⟶
      PresheafOfModules.sheafification
          (R₀ := R.obj) (𝟙 R.obj) ⋙ SheafOfModules.overFunctor R U where
  app P := (overIso R U P).inv
  naturality _ _ f := overIso_inv_naturality R U f

/-- A component of the forward module-sheafification transformation is `overIso`. -/
@[simp, stacks 04IX "forward module-sheafification transformation component"]
theorem overNatTrans_app (P : PresheafOfModules.{z} R.obj) :
    (overNatTrans R U).app P = (overIso R U P).hom := sorry

/-- A component of the inverse module-sheafification transformation is the inverse of `overIso`.
-/
@[simp, stacks 04IX "inverse module-sheafification transformation component"]
theorem overInvNatTrans_app (P : PresheafOfModules.{z} R.obj) :
    (overInvNatTrans R U).app P = (overIso R U P).inv := sorry

/-- The forward and inverse module-sheafification transformations compose to the identity. -/
@[simp, stacks 04IX "module-sheafification transformation forward-inverse law"]
theorem overNatTrans_hom_inv_id :
    overNatTrans R U ≫ overInvNatTrans R U = 𝟙 _ := sorry

/-- The inverse and forward module-sheafification transformations compose to the identity. -/
@[simp, stacks 04IX "module-sheafification transformation inverse-forward law"]
theorem overNatTrans_inv_hom_id :
    overInvNatTrans R U ≫ overNatTrans R U = 𝟙 _ := sorry

/-- Restriction to a slice and module sheafification commute naturally for an arbitrary sheaf
of rings. -/
@[stacks 04IX "natural module-sheafification slice comparison"]
noncomputable def overNatIso :
    PresheafOfModules.sheafification
          (R₀ := R.obj) (𝟙 R.obj) ⋙ SheafOfModules.overFunctor R U ≅
      PresheafOfModules.overFunctor R.obj U ⋙
        PresheafOfModules.sheafification
          (R₀ := (R.over U).obj) (𝟙 (R.over U).obj) where
  hom := overNatTrans R U
  inv := overInvNatTrans R U
  hom_inv_id := overNatTrans_hom_inv_id R U
  inv_hom_id := overNatTrans_inv_hom_id R U

/-- The forward natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 04IX "module-sheafification natural isomorphism hom"]
theorem overNatIso_hom :
    (overNatIso R U).hom = overNatTrans R U := sorry

/-- The inverse natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 04IX "module-sheafification natural isomorphism inverse"]
theorem overNatIso_inv :
    (overNatIso R U).inv = overInvNatTrans R U := sorry

/-- A component of `overNatIso` is the objectwise module-sheafification comparison. -/
@[simp, stacks 04IX "module-sheafification natural isomorphism component"]
theorem overNatIso_app (P : PresheafOfModules.{z} R.obj) :
    (overNatIso R U).app P = overIso R U P := sorry

/-- The forward component of `overNatIso` is the forward objectwise comparison. -/
@[simp, stacks 04IX "module-sheafification natural isomorphism hom component"]
theorem overNatIso_hom_app (P : PresheafOfModules.{z} R.obj) :
    (overNatIso R U).hom.app P = (overIso R U P).hom := sorry

/-- The inverse component of `overNatIso` is the inverse objectwise comparison. -/
@[simp, stacks 04IX "module-sheafification natural isomorphism inverse component"]
theorem overNatIso_inv_app (P : PresheafOfModules.{z} R.obj) :
    (overNatIso R U).inv.app P = (overIso R U P).inv := sorry

end SheafOfModules.Localization.ModuleSheafification
