/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
import StacksCheckRecall

/-!
# Lemma 15.93.1: the category of derived-complete modules

@stack 0GLP

The localization-away predicate is owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness`.  The categorical consequences are owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category`; this file is only the
source-facing check block for the chapter entry.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

section

variable {A : Type u} [CommRing A]

/- Lemma 15.93.1 (Stacks 0GLP): for a ring `A` and ideal `I`, the full subcategory of derived
complete `A`-modules is abelian, has arbitrary limits, and its inclusion into `ModuleCat A` is
exact and preserves limits; for finitely generated `I`, it also has arbitrary colimits and the
inclusion has a left adjoint. -/
@[stacks 0GLP "the category of derived-complete modules"]
#check fun (I : Ideal A) ↦ ModuleCat.DerivedComplete.property.{u, v} I

#check fun (I : Ideal A) ↦
  (ModuleCat.DerivedComplete.category.{u, v} I : Type (max (u + 1) (v + 1)))

#check fun (I : Ideal A) ↦ ModuleCat.DerivedComplete.inclusion.{u, v} I

#check fun (I : Ideal A) ↦
  (ModuleCat.DerivedComplete.Reflector.{u, v} I :
    Type (max (max (v + 1) (u + 1)) v u))

#check fun (I : Ideal A) ↦
  (ModuleCat.DerivedComplete.isWeakSerreClass I :
    ObjectProperty.IsWeakSerreClass (ModuleCat.DerivedComplete.property.{u, v} I))

#check fun (I : Ideal A) ↦
  (ModuleCat.DerivedComplete.abelian I :
    Abelian (ModuleCat.DerivedComplete.category.{u, v} I))

#check fun (I : Ideal A) ↦
  (ModuleCat.DerivedComplete.hasLimits I :
    HasLimits (ModuleCat.DerivedComplete.category.{u, v} I))

#check fun (I : Ideal A) ↦
  (ModuleCat.DerivedComplete.inclusion_exact I :
    exactFunctor (ModuleCat.DerivedComplete.category.{u, v} I) (ModuleCat.{max u v} A)
      (ModuleCat.DerivedComplete.inclusion.{u, v} I))

#check fun (I : Ideal A) ↦
  (ModuleCat.DerivedComplete.inclusion_preservesLimits I :
    PreservesLimitsOfSize (ModuleCat.DerivedComplete.inclusion.{u, v} I))

#check fun (I : Ideal A) (hI : I.FG) ↦
  (ModuleCat.DerivedComplete.hasColimits I hI :
    HasColimits (ModuleCat.DerivedComplete.category.{u, v} I))

#check fun (I : Ideal A) (hI : I.FG) ↦
  (ModuleCat.DerivedComplete.inclusion_isRightAdjoint I hI :
    Functor.IsRightAdjoint (ModuleCat.DerivedComplete.inclusion.{u, v} I))

@[stacks 0GLP "selected reflector onto derived-complete modules"]
#check fun (I : Ideal A) (hI : I.FG) ↦
  (ModuleCat.DerivedComplete.existsReflector I hI :
    Nonempty (ModuleCat.DerivedComplete.Reflector.{u, v} I))

#check fun (I : Ideal A) (hI : I.FG) ↦
  (ModuleCat.DerivedComplete.chosenReflector.{u, v} I hI :
    ModuleCat.DerivedComplete.Reflector.{u, v} I)

#check fun (I : Ideal A) (hI : I.FG) ↦
  (ModuleCat.DerivedComplete.chosenReflector_spec.{u, v} I hI :
    (ModuleCat.DerivedComplete.chosenReflector.{u, v} I hI).toFullSubcategory ⊣
      ModuleCat.DerivedComplete.inclusion.{u, v} I)

#check fun (I : Ideal A) (hI : I.FG)
    (R : ModuleCat.DerivedComplete.Reflector.{u, v} I) ↦
  (ModuleCat.DerivedComplete.chosenReflectionIso I hI R :
    (ModuleCat.DerivedComplete.chosenReflector.{u, v} I hI).reflection ≅ R.reflection)

/- The underlying predicates remain available from the canonical completeness owner. -/
#check fun (f : A) (K : _root_.DerivedCategory (ModuleCat A)) ↦
  (_root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K : Prop)

#check fun (K : _root_.DerivedCategory (ModuleCat A)) (I : Ideal A) ↦
  (_root_.DerivedCategory.IsDerivedCompleteWithRespectTo K I : Prop)

#check fun (K : _root_.DerivedCategory (ModuleCat A)) (I : Ideal A) ↦
  (_root_.DerivedCategory.isDerivedCompleteWithRespectTo_iff K I :
    K.IsDerivedCompleteWithRespectTo I ↔
      ∀ f ∈ I, _root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K)

#check fun (I : Ideal A) ↦ _root_.DerivedCategory.derivedCompleteObjectProperty I

#check fun (M : ModuleCat A) (I : Ideal A) ↦
  (_root_.ModuleCat.IsDerivedCompleteWithRespectTo M I : Prop)

#check fun (I : Ideal A) ↦ _root_.ModuleCat.derivedCompleteObjectProperty I

end

/- Existing chapter consumers used the older `CategoryTheory.*` qualification.  Exporting the
canonical owners keeps that lookup path without introducing a second declaration. -/
namespace CategoryTheory.DerivedCategory

export _root_.DerivedCategory
  (localizationAwayDerivedHomVanishingCondition IsDerivedCompleteWithRespectTo
    isDerivedCompleteWithRespectTo_iff derivedCompleteObjectProperty)

section

variable {A : Type u} [CommRing A]

#check fun (f : A) (K : _root_.DerivedCategory (ModuleCat A)) ↦
  (CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K : Prop)

#check fun (K : _root_.DerivedCategory (ModuleCat A)) (I : Ideal A) ↦
  (CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo K I : Prop)

end

end CategoryTheory.DerivedCategory

namespace CategoryTheory.ModuleCat

export _root_.ModuleCat (IsDerivedCompleteWithRespectTo derivedCompleteObjectProperty)

section

variable {A : Type u} [CommRing A]

#check fun (M : _root_.ModuleCat A) (I : Ideal A) ↦
  (CategoryTheory.ModuleCat.IsDerivedCompleteWithRespectTo M I : Prop)

end

end CategoryTheory.ModuleCat

end
