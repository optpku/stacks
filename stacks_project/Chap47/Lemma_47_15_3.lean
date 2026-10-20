/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Duality
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
variable (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
variable (ω : DerivedCategory (ModuleCat.{u} A))
variable (hω : ω.IsDualizingComplex H)

/- Lemma 47.15.3 (1): derived internal Hom into a dualizing complex is an
anti-equivalence on complexes with finite cohomology. -/
@[stacks 0A7C] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.coherentDuality_isEquivalence H ω hω :
    (CategoryTheory.DerivedCategory.IsDualizingComplex.coherentDuality H ω hω).IsEquivalence)

/- Lemma 47.15.3 (2): derived internal Hom into a dualizing complex exchanges the
bounded-below and bounded-above categories of complexes with finite cohomology. -/
@[stacks 0A7C] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.plusDuality_isEquivalence H ω hω :
    (CategoryTheory.DerivedCategory.IsDualizingComplex.plusDuality H ω hω).IsEquivalence)

/- Lemma 47.15.3 (3): derived internal Hom into a dualizing complex is an
anti-equivalence on bounded complexes with finite cohomology. -/
@[stacks 0A7C] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.boundedDuality_isEquivalence H ω hω :
    (CategoryTheory.DerivedCategory.IsDualizingComplex.boundedDuality H ω hω).IsEquivalence)

/- Lemma 47.15.3 (4): the canonical bidual transformation exhibits double duality as
naturally isomorphic to the identity. -/
@[stacks 0A7C] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.coherentBidual_isIso H ω hω :
    IsIso (CategoryTheory.DerivedCategory.IsDualizingComplex.coherentBidual H ω hω))
