/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-
Lemma 13.13.4 is a canonical recall of the neutral finite-filtered homological-kernel and
localization API in `ReasLib.CategoryTheory.Filtration.Derived.Triangulated`.
-/

/- Lemma 13.13.4 (1): filtered acyclic complexes form a strictly full subcategory. -/
@[stacks 05S1] #check
  (FilteredObject.FiniteDerived.Acyclic.isClosedUnderIsomorphisms 𝒜)

/- Lemma 13.13.4 (2): filtered acyclic complexes are stable under retracts. -/
@[stacks 05S1] #check
  (FilteredObject.FiniteDerived.Acyclic.isStableUnderRetracts 𝒜)

/- Lemma 13.13.4 (3): filtered acyclic complexes form a triangulated subcategory. -/
@[stacks 05S1] #check
  (FilteredObject.FiniteDerived.Acyclic.isTriangulated 𝒜)

/- Lemma 13.13.4 (4): the Verdier morphism property associated to filtered acyclic complexes is
exactly the filtered quasi-isomorphism property. -/
@[stacks 05S1] #check
  (FilteredObject.FiniteDerived.Acyclic.trW_eq_quasiIso 𝒜)

/- Lemma 13.13.4 (5): filtered quasi-isomorphisms form a saturated multiplicative system. -/
@[stacks 05S1] #check
  (FilteredObject.FiniteDerived.QuasiIso.isSaturated 𝒜)

/- Lemma 13.13.4 (6): localization at filtered quasi-isomorphisms has the filtered acyclic
complexes as its kernel. -/
@[stacks 05S1] #check
  (FilteredObject.FiniteDerived.Acyclic.kernel_eq 𝒜)

/- Lemma 13.13.4 (7): associated-graded degree-zero homology factors through localization at
filtered quasi-isomorphisms. -/
@[stacks 05S1] #check
  (FilteredObject.FiniteDerived.Acyclic.existsHomologyFactorization 𝒜)

end CategoryTheory
