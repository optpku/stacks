/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded.Localization
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointwise Computation by Bounded-Below K-Injectives

This leaf is the bounded-below counterpart of `Functor.KInjective`. It is
formulated directly for the localization of `HomotopyCategory.Plus` at
quasi-isomorphisms, so it does not choose a derived-category model or require
enough injectives. Its endpoint full-faithfulness datum specializes the neutral
terminal-denominator and derived-computation APIs.
-/

open CategoryTheory Limits ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.KInjective.Bounded

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [Category.{v₂} 𝒟]

/-- Stacks 05TH: localizing bounded-below homotopy complexes at
quasi-isomorphisms is bijective on maps into a bounded-below K-injective
object. -/
@[stacks 05TH]
theorem Localization.map_bijective
    (K I : HomotopyCategory.Plus 𝒜) [CochainComplex.IsKInjective I.obj.as] :
    Function.Bijective
      ((MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).map :
        (K ⟶ I) →
          ((MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj K ⟶
            (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj I)) := sorry

/-- The explicit preimage of a localized morphism into a bounded-below K-injective homotopy
object. It is transported from Mathlib's inverse for `DerivedCategory.Plus.Qh.map`. -/
@[stacks 05TH]
noncomputable def Localization.preimage
    (K I : HomotopyCategory.Plus 𝒜) [CochainComplex.IsKInjective I.obj.as]
    (f : (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj K ⟶
      (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj I) : K ⟶ I :=
  (HomotopyCategory.Plus.KInjective.homEquiv
    (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)) K I).symm f

/-- Mapping `quasiIsoLocalizationPreimage` back to the canonical bounded-below localization
recovers the localized morphism. -/
@[stacks 05TH]
theorem Localization.map_preimage
    (K I : HomotopyCategory.Plus 𝒜) [CochainComplex.IsKInjective I.obj.as]
    (f : (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj K ⟶
      (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj I) :
    (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).map
      (Localization.preimage K I f) = f := sorry

/-- Taking the bounded-below localization preimage of a mapped homotopy morphism recovers the
original morphism into the K-injective object. -/
@[stacks 05TH]
theorem Localization.preimage_map
    (K I : HomotopyCategory.Plus 𝒜) [CochainComplex.IsKInjective I.obj.as]
    (f : K ⟶ I) :
    Localization.preimage K I
      ((MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).map f) = f := sorry

/-- The bounded-below localization is targetwise fully faithful at a K-injective object. This is
the reusable owner of its inverse map and inverse laws. -/
@[stacks 05TH]
noncomputable def Localization.fullyFaithfulTo
    (I : HomotopyCategory.Plus 𝒜) [CochainComplex.IsKInjective I.obj.as] :
    (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).FullyFaithfulTo I :=
  HomotopyCategory.Plus.KInjective.fullyFaithfulTo
    (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)) I

/-- Morphisms into a bounded-below K-injective homotopy object are explicitly equivalent before
and after canonical quasi-isomorphism localization. -/
@[stacks 05TH]
noncomputable def Localization.homEquiv
    (K I : HomotopyCategory.Plus 𝒜) [CochainComplex.IsKInjective I.obj.as] :
    (K ⟶ I) ≃
      ((MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj K ⟶
        (MorphismProperty.Q (HomotopyCategory.Plus.quasiIso 𝒜)).obj I) :=
  (Localization.fullyFaithfulTo I).homEquiv

/-- Stacks 05TH: a bounded-below K-injective homotopy object computes the
pointwise right-derived value of every functor out of `K⁺(𝒜)`. -/
@[stacks 05TH]
noncomputable instance computesAt
    (F : HomotopyCategory.Plus 𝒜 ⥤ 𝒟) (I : HomotopyCategory.Plus 𝒜)
    [CochainComplex.IsKInjective I.obj.as] :
    RightDerived.ComputesAt F (HomotopyCategory.Plus.quasiIso 𝒜) I := sorry

/-- Stacks 05TH: a bounded-below cochain complex of injectives computes the
pointwise right-derived value after passing to the bounded-below homotopy
category. This cochain-level form avoids a caller-side instance bridge. -/
@[stacks 05TH]
theorem computesAtOfInjectivePlus
    (F : HomotopyCategory.Plus 𝒜 ⥤ 𝒟) (I : CochainComplex.InjectivePlus 𝒜) :
    RightDerived.ComputesAt F (HomotopyCategory.Plus.quasiIso 𝒜)
      ((HomotopyCategory.Plus.quotient 𝒜).obj I) := sorry



end CategoryTheory.Functor.KInjective.Bounded
