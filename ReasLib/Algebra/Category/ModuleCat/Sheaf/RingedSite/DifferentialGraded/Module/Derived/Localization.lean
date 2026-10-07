module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Basic

/-!
# Universal property of the DG derived category

This file specializes the localization universal property to the intrinsic homotopy category of
differential graded module sheaves.  The specialized lift, its factorization isomorphism, and
lifts of natural transformations avoid repeating the canonical functor `Qh` and the DG
quasi-isomorphism class at every use site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  Localization lifts must reuse the intrinsic homotopy owner's choice.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w x

namespace SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Localization

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))
variable {E : Type w} [Category.{x} E]

/-- The functor on the DG derived category induced by a functor on the intrinsic DG homotopy
category which inverts DG homotopy quasi-isomorphisms. -/
noncomputable def lift (F : K ℤ Mod(𝒜, d) ⥤ E)
    (hF : (Homotopy.quasiIso 𝒜).IsInvertedBy F) :
    DerivedCategory 𝒜 ⥤ E :=
  CategoryTheory.Localization.lift F hF (Qh 𝒜)

/-- The canonical factorization of a quasi-isomorphism-inverting functor through the DG derived
category. -/
noncomputable def facIso (F : K ℤ Mod(𝒜, d) ⥤ E)
    (hF : (Homotopy.quasiIso 𝒜).IsInvertedBy F) :
    Qh 𝒜 ⋙ lift 𝒜 F hF ≅ F :=
  CategoryTheory.Localization.fac F hF (Qh 𝒜)

/-- The specialized DG-derived lift carries the canonical lifting structure for `Qh`. -/
noncomputable instance liftingLift (F : K ℤ Mod(𝒜, d) ⥤ E)
    (hF : (Homotopy.quasiIso 𝒜).IsInvertedBy F) :
    CategoryTheory.Localization.Lifting (Qh 𝒜) (Homotopy.quasiIso 𝒜) F
      (lift 𝒜 F hF) :=
  CategoryTheory.Localization.liftingLift F hF (Qh 𝒜)

namespace facIso

/-- Naturality of the forward DG-derived factorization comparison. -/
@[reassoc (attr := simp)]
theorem hom_naturality (F : K ℤ Mod(𝒜, d) ⥤ E)
    (hF : (Homotopy.quasiIso 𝒜).IsInvertedBy F)
    {X Y : K ℤ Mod(𝒜, d)} (f : X ⟶ Y) :
    (lift 𝒜 F hF).map ((Qh 𝒜).map f) ≫ (facIso 𝒜 F hF).hom.app Y =
      (facIso 𝒜 F hF).hom.app X ≫ F.map f := sorry

/-- Naturality of the inverse DG-derived factorization comparison. -/
@[reassoc (attr := simp)]
theorem inv_naturality (F : K ℤ Mod(𝒜, d) ⥤ E)
    (hF : (Homotopy.quasiIso 𝒜).IsInvertedBy F)
    {X Y : K ℤ Mod(𝒜, d)} (f : X ⟶ Y) :
    F.map f ≫ (facIso 𝒜 F hF).inv.app Y =
      (facIso 𝒜 F hF).inv.app X ≫
        (lift 𝒜 F hF).map ((Qh 𝒜).map f) := sorry

end facIso

/-- The natural transformation on DG-derived lifts induced by a natural transformation before
localization. -/
noncomputable def liftNatTrans {F₁ F₂ : K ℤ Mod(𝒜, d) ⥤ E}
    (hF₁ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₁)
    (hF₂ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₂) (t : F₁ ⟶ F₂) :
    lift 𝒜 F₁ hF₁ ⟶ lift 𝒜 F₂ hF₂ :=
  CategoryTheory.Localization.liftNatTrans (Qh 𝒜) (Homotopy.quasiIso 𝒜)
    F₁ F₂ (lift 𝒜 F₁ hF₁) (lift 𝒜 F₂ hF₂) t

namespace liftNatTrans

/-- The component of a lifted natural transformation on an object represented by the DG
homotopy category. -/
@[simp]
theorem app_Qh {F₁ F₂ : K ℤ Mod(𝒜, d) ⥤ E}
    (hF₁ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₁)
    (hF₂ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₂) (t : F₁ ⟶ F₂)
    (X : K ℤ Mod(𝒜, d)) :
    (liftNatTrans 𝒜 hF₁ hF₂ t).app ((Qh 𝒜).obj X) =
      (facIso 𝒜 F₁ hF₁).hom.app X ≫ t.app X ≫
        (facIso 𝒜 F₂ hF₂).inv.app X := sorry

/-- Lifting the identity natural transformation gives the identity of the DG-derived lift. -/
@[simp]
theorem id (F : K ℤ Mod(𝒜, d) ⥤ E)
    (hF : (Homotopy.quasiIso 𝒜).IsInvertedBy F) :
    liftNatTrans 𝒜 hF hF (𝟙 F) = 𝟙 (lift 𝒜 F hF) := sorry

/-- Lifting a composite of natural transformations is the composite of their DG-derived
lifts. -/
@[reassoc]
theorem comp {F₁ F₂ F₃ : K ℤ Mod(𝒜, d) ⥤ E}
    (hF₁ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₁)
    (hF₂ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₂)
    (hF₃ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₃)
    (t₁₂ : F₁ ⟶ F₂) (t₂₃ : F₂ ⟶ F₃) :
    liftNatTrans 𝒜 hF₁ hF₂ t₁₂ ≫ liftNatTrans 𝒜 hF₂ hF₃ t₂₃ =
      liftNatTrans 𝒜 hF₁ hF₃ (t₁₂ ≫ t₂₃) := sorry

end liftNatTrans

/-- The natural isomorphism on DG-derived lifts induced by a natural isomorphism before
localization. -/
noncomputable def liftNatIso {F₁ F₂ : K ℤ Mod(𝒜, d) ⥤ E}
    (hF₁ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₁)
    (hF₂ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₂) (e : F₁ ≅ F₂) :
    lift 𝒜 F₁ hF₁ ≅ lift 𝒜 F₂ hF₂ :=
  CategoryTheory.Localization.liftNatIso (Qh 𝒜) (Homotopy.quasiIso 𝒜)
    F₁ F₂ (lift 𝒜 F₁ hF₁) (lift 𝒜 F₂ hF₂) e

namespace liftNatIso

/-- The forward component of a lifted natural isomorphism on an object represented by the DG
homotopy category. -/
@[simp]
theorem hom_app_Qh {F₁ F₂ : K ℤ Mod(𝒜, d) ⥤ E}
    (hF₁ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₁)
    (hF₂ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₂) (e : F₁ ≅ F₂)
    (X : K ℤ Mod(𝒜, d)) :
    (liftNatIso 𝒜 hF₁ hF₂ e).hom.app ((Qh 𝒜).obj X) =
      (facIso 𝒜 F₁ hF₁).hom.app X ≫ e.hom.app X ≫
        (facIso 𝒜 F₂ hF₂).inv.app X := sorry

/-- The inverse component of a lifted natural isomorphism on an object represented by the DG
homotopy category. -/
@[simp]
theorem inv_app_Qh {F₁ F₂ : K ℤ Mod(𝒜, d) ⥤ E}
    (hF₁ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₁)
    (hF₂ : (Homotopy.quasiIso 𝒜).IsInvertedBy F₂) (e : F₁ ≅ F₂)
    (X : K ℤ Mod(𝒜, d)) :
    (liftNatIso 𝒜 hF₁ hF₂ e).inv.app ((Qh 𝒜).obj X) =
      (facIso 𝒜 F₂ hF₂).hom.app X ≫ e.inv.app X ≫
        (facIso 𝒜 F₁ hF₁).inv.app X := sorry

end liftNatIso

end

end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.Localization
