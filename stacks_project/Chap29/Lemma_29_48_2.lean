/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/-!
# Lemma 29.48.2

The reusable finite-locally-free characterization API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations`.
-/

/- Lemma 29.48.2 (1): finite local freeness is finite, flat, and locally of finite presentation. -/
@[stacks 02KB] #check
  (AlgebraicGeometry.finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S},
      IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f)

/- Lemma 29.48.2 (2): on a locally Noetherian base, finite plus flat is sufficient. -/
@[stacks 02KB] #check
  (AlgebraicGeometry.finiteLocallyFree_iff_isFinite_and_flat :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S],
      IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f)
