/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Beauville-Laszlo Equivalence for Glueable Modules

Restricting the canonical single-principal-open formal-gluing functor to modules whose module Cech
sequence is short exact gives the Beauville-Laszlo equivalence for a gluing pair.

@stack 0BP2
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace LocalizedModule.Away.FormalGluing.Single

variable {R : Type u} [CommRing R]

/-- The full-subcategory property of modules glueable for `(R → S, f)`. -/
@[stacks 0BP2 "Beauville-Laszlo glueable module property"]
abbrev glueableProperty (S : Type u) [CommRing S] [Algebra R S]
    (f : R) : ObjectProperty (ModuleCat R) :=
  fun M ↦ (beauvilleLaszloModuleCechSequence S M f).ShortExact

/-- The canonical formal-gluing functor restricted to glueable modules. -/
@[stacks 0BP2 "Beauville-Laszlo functor on glueable modules"]
noncomputable abbrev glueableFunctor
    (S : Type u) [CommRing S] [Algebra R S] (f : R) :
    (glueableProperty S f).FullSubcategory ⥤
      CategoryTheory.Limits.CategoricalPullback
        (ModuleCat.extendScalars
          (algebraMap S (Localization.Away (algebraMap R S f))))
        (ModuleCat.extendScalars
          (LocalizedModule.Away.FormalGluing.Single.overlapMap
            (algebraMap R S) f)) :=
  (glueableProperty S f).ι ⋙ functor (algebraMap R S) f

/-- Theorem 15.91.16 (0BP2): for a Beauville-Laszlo gluing pair, canonical formal gluing is an
equivalence from glueable modules to the category of gluing data. -/
@[stacks 0BP2, stacks 0BP8 "Theorem 15.91.16"]
theorem glueableFunctor_isEquivalence
    (S : Type u) [CommRing S] [Algebra R S] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R S) f) :
    Functor.IsEquivalence (glueableFunctor S f) := sorry

end LocalizedModule.Away.FormalGluing.Single
