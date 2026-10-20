module

public import ReasLib.CategoryTheory.Sites.TypeSheafification
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.Logic.Small.Basic

/-!
# ULift and type-valued sheafification

This file records the universe-change API for `Type`-valued sheafification.
It contains only statements stable under arbitrary applications of `ULift`;
concrete representative and image-sieve calculations remain implementation
details of their proofs.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w w'

namespace CategoryTheory.GrothendieckTopology

/-- Composition with the canonical `ULift` functor preserves the sheaf
condition for type-valued presheaves. -/
instance uliftFunctor_hasSheafCompose_type
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose
      (uliftFunctor.{w', w} : Type w ⥤ Type (max w w')) := sorry

/-- Local injectivity of a type-valued presheaf map is reflected by
whiskering with `ULift`. -/
theorem locallyInjective_of_whisker_ulift
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J
      (Functor.whiskerRight f
        (uliftFunctor.{w', w} : Type w ⥤ Type (max w w')))] :
    Presheaf.IsLocallyInjective J f := sorry

/-- Local surjectivity of a type-valued presheaf map is reflected by
whiskering with `ULift`. -/
theorem locallySurjective_of_whisker_ulift
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f
        (uliftFunctor.{w', w} : Type w ⥤ Type (max w w')))] :
    Presheaf.IsLocallySurjective J f := sorry

/-- If every small type-valued sheafification unit is locally injective,
then changing values by `ULift` preserves sheafification.  The locally
surjective half is supplied by
`toSheafify_isLocallySurjective_type`. -/
theorem uliftFunctor_preservesSheafification_of_toSheafify_isLocallyInjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [HasWeakSheafify J (Type (max w w'))]
    (h_injective :
      ∀ P : Cᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P)) :
    J.PreservesSheafification
      (uliftFunctor.{w', w} : Type w ⥤ Type (max w w')) := sorry

/-- If weak equivalences are locally bijective before and after a universe
lift, then `ULift` preserves sheafification. -/
theorem uliftFunctor_preservesSheafification_of_WEqualsLocallyBijective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [HasWeakSheafify J (Type (max w w'))]
    [J.WEqualsLocallyBijective (Type w)]
    [J.WEqualsLocallyBijective (Type (max w w'))] :
    J.PreservesSheafification
      (uliftFunctor.{w', w} : Type w ⥤ Type (max w w')) := sorry

/-- Multicospan limits and cover-indexed colimits in the source type universe
give sheafification preservation for the canonical lift into the universe
containing the site. -/
theorem uliftFunctor_preservesSheafification_of_multicospanLimits_and_coverColimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [HasWeakSheafify J (Type (max w (max u v)))]
    [∀ M : MulticospanShape.{max v u, max v u},
      HasLimitsOfShape (WalkingMulticospan M) (Type w)]
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ (Type w)] :
    J.PreservesSheafification
      (uliftFunctor.{max u v, w} : Type w ⥤ Type (max w (max u v))) := sorry

/-- Smallness of the multicospan and cover-indexing categories in the source
type universe gives sheafification preservation for the canonical universe
lift. -/
theorem uliftFunctor_preservesSheafification_of_smallMulticospans_and_covers
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [HasWeakSheafify J (Type (max w (max u v)))]
    [∀ M : MulticospanShape.{max v u, max v u},
      Small.{w} (WalkingMulticospan M)]
    [∀ X : C, Small.{w} (J.Cover X)ᵒᵖ] :
    J.PreservesSheafification
      (uliftFunctor.{max u v, w} : Type w ⥤ Type (max w (max u v))) := sorry

end CategoryTheory.GrothendieckTopology
