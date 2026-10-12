/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.ObjectProperty.Reflector
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completeness of module complexes

This file owns the derived completeness predicate for an ideal in the derived category of modules.
It is formulated through vanishing of morphisms after restriction of scalars to localizations away
from elements of the ideal.

@stack 0G3E
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

/-- Every morphism from a derived module over `A_f` to `K` becomes zero after restriction of
scalars along `A → A_f`. -/
@[stacks 091P "localization-away derived-Hom vanishing"]
def localizationAwayDerivedHomVanishingCondition
    (f : A) (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
    Subsingleton
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
        K)

/-- A derived `A`-module is derived complete with respect to an ideal `I` when the
localization-away vanishing condition holds for every element of `I`. -/
@[stacks 091S "(1), derived-complete complex"]
def IsDerivedCompleteWithRespectTo
    (K : DerivedCategory (ModuleCat A)) (I : Ideal A) : Prop :=
  ∀ f ∈ I, localizationAwayDerivedHomVanishingCondition f K

/-- Derived completeness with respect to `I` is exactly the family of localization-away
vanishing conditions indexed by elements of `I`. -/
theorem isDerivedCompleteWithRespectTo_iff
    (K : DerivedCategory (ModuleCat A)) (I : Ideal A) :
    K.IsDerivedCompleteWithRespectTo I ↔
      ∀ f ∈ I, localizationAwayDerivedHomVanishingCondition f K := sorry

/-- The object property on `DerivedCategory (ModuleCat A)` selecting complexes derived complete
with respect to `I`. -/
@[stacks 091S "derived-complete object property"]
abbrev derivedCompleteObjectProperty (I : Ideal A) :
    ObjectProperty (DerivedCategory (ModuleCat A)) :=
  fun K ↦ K.IsDerivedCompleteWithRespectTo I

namespace DerivedCompletion

variable {I : Ideal A}

/-- A chosen reflector from the derived category of `A`-modules to the full subcategory of
objects derived complete with respect to `I`. -/
@[stacks 0G3E "derived-completion reflector"]
abbrev Reflector (I : Ideal A) :=
  ObjectProperty.Reflector (derivedCompleteObjectProperty I)

namespace Reflector

/-- The derived-completion endofunctor induced by a chosen reflector. -/
@[stacks 0G3E "derived-completion endofunctor"]
def completion (R : Reflector I) :
    DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A) :=
  ObjectProperty.Reflector.reflection R

/-- The derived completion of an object under a chosen reflector. -/
@[stacks 0G3E "derived-completion object"]
def obj (R : Reflector I) (K : DerivedCategory (ModuleCat A)) :
    DerivedCategory (ModuleCat A) :=
  R.completion.obj K

/-- The `n`-th cohomology module of the derived completion of `K`. -/
@[stacks 0G3E "cohomology of a derived completion"]
def cohomology (R : Reflector I) (n : ℤ) (K : DerivedCategory (ModuleCat A)) :
    ModuleCat A :=
  (homologyFunctor (ModuleCat A) n).obj (R.obj K)

/-- The universal map from an object to its derived completion. -/
@[stacks 0G3E "derived-completion unit"]
def unit (R : Reflector I) :
    𝟭 (DerivedCategory (ModuleCat A)) ⟶ R.completion :=
  ObjectProperty.Reflector.unit R

/-- The universal lift from the reflection of `K` to a derived-complete target `L`. -/
@[stacks 0G3E "derived-completion universal lift"]
def lift (R : Reflector I) {K L : DerivedCategory (ModuleCat A)}
    (hL : L.IsDerivedCompleteWithRespectTo I) (f : K ⟶ L) :
    R.obj K ⟶ L :=
  ((R.adjunction.homEquiv K ⟨L, hL⟩).symm f).hom

/-- The completion unit followed by its universal lift is the original morphism. -/
@[stacks 0G3E "derived-completion universal lift specification"]
theorem unit_comp_lift (R : Reflector I) {K L : DerivedCategory (ModuleCat A)}
    (hL : L.IsDerivedCompleteWithRespectTo I) (f : K ⟶ L) :
    R.unit.app K ≫ R.lift hL f = f := sorry

/-- A reflector takes every object to one derived complete with respect to its ideal. -/
theorem isDerivedComplete (R : Reflector I) (K : DerivedCategory (ModuleCat A)) :
    (R.obj K).IsDerivedCompleteWithRespectTo I := sorry

/-- The canonical comparison between the completion endofunctors induced by two reflectors onto
the same full subcategory. -/
@[stacks 0G3E "uniqueness of the derived-completion endofunctor"]
noncomputable def completionIso (R S : Reflector I) :
    R.completion ≅ S.completion :=
  Functor.isoWhiskerRight (R.adjunction.leftAdjointUniq S.adjunction)
    (derivedCompleteObjectProperty I).ι

/-- The canonical comparison of two reflectors identifies their universal completion maps. -/
@[stacks 0G3E "uniqueness of the derived-completion unit"]
theorem unit_comp_completionIso_hom (R S : Reflector I) :
    R.unit ≫ (R.completionIso S).hom = S.unit := sorry

end Reflector

/-- A finitely generated ideal admits a reflector from `D(A)` onto the full subcategory of
derived-complete objects. -/
@[stacks 0G3E "existence of derived completion"]
theorem existsReflector (I : Ideal A) (hI : I.FG) :
    Nonempty (Reflector I) := sorry

/-- A selected derived-completion reflector for a finitely generated ideal.  Consumers should use
its reflector API and the comparison isomorphism rather than inspect this choice. -/
@[stacks 0G3E "selected derived-completion reflector"]
noncomputable def chosenReflector (I : Ideal A) (hI : I.FG) : Reflector I :=
  Classical.choice (existsReflector I hI)

/-- The selected derived-completion reflector has the defining reflection adjunction. -/
@[stacks 0G3E "selected derived-completion reflector specification"]
noncomputable def chosenReflector_spec (I : Ideal A) (hI : I.FG) :
    (chosenReflector I hI).toFullSubcategory ⊣ (derivedCompleteObjectProperty I).ι :=
  (chosenReflector I hI).adjunction

/-- The completion functor of the selected reflector is canonically isomorphic to that of any
other reflector onto the derived-complete subcategory. -/
@[stacks 0G3E "selected derived-completion reflector independence"]
noncomputable def chosenReflectorIso (I : Ideal A) (hI : I.FG) (R : Reflector I) :
    (chosenReflector I hI).completion ≅ R.completion :=
  (chosenReflector I hI).completionIso R

/-- The comparison from the selected reflector to any other reflector preserves the universal
completion map. -/
@[stacks 0G3E "selected derived-completion unit independence"]
theorem chosenReflectorIso_unit (I : Ideal A) (hI : I.FG) (R : Reflector I) :
    (chosenReflector I hI).unit ≫ (chosenReflectorIso I hI R).hom = R.unit := sorry

end DerivedCompletion

/-- The derived-completion endofunctor selected by a finite generating proof for `I`. -/
@[stacks 0G3E "derived-completion endofunctor"]
noncomputable def derivedCompletion (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A) :=
  (DerivedCompletion.chosenReflector I hI).completion

/-- The derived completion of `K` with respect to a finitely generated ideal `I`. -/
@[stacks 0G3E "derived-completion object"]
noncomputable def derivedCompletionOf (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat A)) : DerivedCategory (ModuleCat A) :=
  (derivedCompletion I hI).obj K

-- The textbook notation records both the ideal and the finite-generation witness used by the
-- selected reflector.
notation:max K:max "^∧[" I:max ", " hI:max "]" => derivedCompletionOf I hI K

/-- The universal map from `K` to its selected derived completion. -/
@[stacks 0G3E "map to derived completion"]
noncomputable def toDerivedCompletion (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat A)) : K ⟶ K^∧[I, hI] :=
  (DerivedCompletion.chosenReflector I hI).unit.app K

/-- The universal maps to derived completion are functorial in the source object. -/
@[stacks 0G3E "functoriality of the map to derived completion"]
theorem toDerivedCompletion_naturality (I : Ideal A) (hI : I.FG)
    {K L : DerivedCategory (ModuleCat A)} (f : K ⟶ L) :
    f ≫ toDerivedCompletion I hI L =
      toDerivedCompletion I hI K ≫ (derivedCompletion I hI).map f := sorry

/-- The selected derived completion is derived complete with respect to its defining ideal. -/
@[stacks 0G3E "derived completeness of derived completion"]
theorem derivedCompletionOf_isDerivedComplete (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat A)) :
    (K^∧[I, hI]).IsDerivedCompleteWithRespectTo I := sorry

namespace DerivedCompletion

/-- The canonical factorization of a morphism from `K` to a derived-complete target through the
selected derived completion of `K`. -/
@[stacks 0G3E "selected derived-completion universal lift"]
noncomputable def lift (I : Ideal A) (hI : I.FG)
    {K L : DerivedCategory (ModuleCat A)}
    (hL : L.IsDerivedCompleteWithRespectTo I) (f : K ⟶ L) :
    derivedCompletionOf I hI K ⟶ L :=
  (chosenReflector I hI).lift hL f

/-- The selected completion unit followed by the canonical lift is the original morphism. -/
@[stacks 0G3E "selected derived-completion universal lift specification"]
theorem toDerivedCompletion_comp_lift (I : Ideal A) (hI : I.FG)
    {K L : DerivedCategory (ModuleCat A)}
    (hL : L.IsDerivedCompleteWithRespectTo I) (f : K ⟶ L) :
    toDerivedCompletion I hI K ≫ lift I hI hL f = f := sorry

end DerivedCompletion

end

end DerivedCategory

namespace ModuleCat

section

variable {A : Type u} [CommRing A]

/-- An `A`-module is derived complete with respect to `I` when its degree-zero derived object is
derived complete with respect to `I`. -/
@[stacks 091S "(2), derived-complete module"]
abbrev IsDerivedCompleteWithRespectTo
    (M : ModuleCat.{max u v, u} A) (I : Ideal A) : Prop :=
  _root_.DerivedCategory.IsDerivedCompleteWithRespectTo
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v, u} A) (0 : ℤ)).obj M) I

/-- The object property on `ModuleCat A` selecting modules derived complete with respect to `I`.
-/
@[stacks 091S "derived-complete module object property"]
abbrev derivedCompleteObjectProperty (I : Ideal A) :
    ObjectProperty (ModuleCat.{max u v, u} A) :=
  fun M ↦ M.IsDerivedCompleteWithRespectTo I

end

end ModuleCat
