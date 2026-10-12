/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.KoszulLimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# The powered-Koszul derived-completion reflector

For a finite family `f : Fin r → A`, this file turns a functor whose unit components are the
canonical powered-Koszul derived-limit comparisons into a reflector onto the full subcategory of
derived-complete objects.  The unit, counit, adjunction, and reflector remain explicit data.

@stack 0920
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.KoszulLimit.Reflector

variable {A : Type u} [CommRing A] {r : ℕ}

variable (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)

/-- The family of canonical powered-Koszul derived-limit comparisons carried by the components
of a proposed reflector unit. -/
@[stacks 0920 "powered-Koszul comparison unit"]
abbrev ComparisonUnit
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι) :=
  ∀ K : DerivedCategory (ModuleCat.{u} A), Comparison f K (L.obj K).obj (eta.app K)

/-- A powered-Koszul comparison unit is an isomorphism on every derived-complete object. -/
@[stacks 0920 "comparison unit is an isomorphism on complete objects"]
theorem unitApp_isIso
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta) {K : DerivedCategory (ModuleCat.{u} A)}
    (hK : K.IsDerivedCompleteWithRespectTo I) :
    IsIso (eta.app K) := sorry

/-- The comparison component on an object of the derived-complete full subcategory, bundled as
an isomorphism in the ambient derived category. -/
@[stacks 0920 "comparison isomorphism on a complete object"]
noncomputable def unitAppIso
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta)
    (E : (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory) :
    E.obj ≅ (L.obj E.obj).obj :=
  @asIso _ _ _ _ (eta.app E.obj) (unitApp_isIso f L eta heta E.property)

/-- The counit component on a derived-complete object is the inverse comparison map, lifted
through the fully faithful inclusion. -/
@[stacks 0920 "powered-Koszul reflector counit component"]
noncomputable def counitApp
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta)
    (E : (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory) :
    L.obj E.obj ⟶ E :=
  (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι.preimage
    ((unitAppIso f L eta heta E).symm.hom)

/-- Forgetting the powered-Koszul reflector counit component recovers the inverse comparison
morphism in the ambient derived category. -/
@[stacks 0920 "ambient formula for the powered-Koszul reflector counit"]
theorem counitApp_map
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta)
    (E : (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory) :
    (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι.map
        (counitApp f L eta heta E) =
      (unitAppIso f L eta heta E).symm.hom := sorry

/-- The powered-Koszul reflector counit components are natural on the full subcategory of
derived-complete objects. -/
@[stacks 0920 "naturality of the powered-Koszul reflector counit"]
theorem counit_natural
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta)
    {E₁ E₂ : (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory}
    (phi : E₁ ⟶ E₂) :
    L.map ((_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι.map phi) ≫
        counitApp f L eta heta E₂ =
      counitApp f L eta heta E₁ ≫ phi := sorry

/-- The counit from inclusion followed by powered-Koszul reflection to the identity functor on
derived-complete objects. -/
@[stacks 0920 "powered-Koszul reflector counit"]
noncomputable def counit
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta) :
    (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι ⋙ L ⟶
      𝟭 ((_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory) where
  app E := counitApp f L eta heta E
  naturality {E₁ E₂} phi :=
    counit_natural f L eta heta (E₁ := E₁) (E₂ := E₂) phi

/-- The left triangle identity for the powered-Koszul comparison unit and its explicit counit. -/
@[stacks 0920 "left triangle identity for the powered-Koszul reflector"]
theorem left_triangle
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta) :
    Functor.whiskerRight eta L ≫
        (Functor.associator L
          (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι L).hom ≫
        Functor.whiskerLeft L (counit f L eta heta) =
      NatTrans.id (𝟭 (DerivedCategory (ModuleCat.{u} A)) ⋙ L) := sorry

/-- The right triangle identity for the powered-Koszul comparison unit and its explicit counit. -/
@[stacks 0920 "right triangle identity for the powered-Koszul reflector"]
theorem right_triangle
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta) :
    Functor.whiskerLeft
        (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι eta ≫
        (Functor.associator
          (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι L
          (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι).inv ≫
        Functor.whiskerRight (counit f L eta heta)
          (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι =
      NatTrans.id
        ((_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι ⋙
          𝟭 (DerivedCategory (ModuleCat.{u} A))) := sorry

/-- Lemma 15.92.18 (0920): a functor equipped with the canonical powered-Koszul derived-limit
comparison as its unit is left adjoint to the inclusion of derived-complete objects. -/
@[stacks 0920 "Lemma 15.92.18"]
noncomputable def adjunction
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta) :
    L ⊣ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι :=
  Adjunction.mkOfUnitCounit
    { unit := eta
      counit := counit f L eta heta
      left_triangle := left_triangle f L eta heta
      right_triangle := right_triangle f L eta heta }

/-- The reflector onto derived-complete objects determined by a powered-Koszul comparison unit. -/
@[stacks 0920 "powered-Koszul derived-completion reflector"]
noncomputable def reflector
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta) :
    _root_.DerivedCategory.DerivedCompletion.Reflector.{u, u} I where
  toFullSubcategory := L
  adjunction := adjunction f L eta heta

/-- The unit of the powered-Koszul reflector is the supplied canonical comparison
transformation. -/
@[stacks 0920 "unit of the powered-Koszul derived-completion reflector"]
theorem reflector_unit
    (L : DerivedCategory (ModuleCat.{u} A) ⥤
      (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).FullSubcategory)
    (eta : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶
      L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty.{u, u} I).ι)
    (heta : ComparisonUnit f L eta) :
    (reflector f L eta heta).unit = eta := sorry

end CategoryTheory.DerivedCategory.KoszulLimit.Reflector
