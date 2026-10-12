/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap79.Lemma_79_9_6_Restriction
public import stacks_project.Chap79.Lemma_79_9_6_FieldPoints

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace

universe u

/-
Lemma 79.9.6: in Situation 79.9.2, every point `r` of `|R|` lifts after restriction
along some algebraically closed extension `k'/k` to a morphism `r' : Spec(k') ⟶ R'`
that maps to `r` under `R' ⟶ R`, with `s' ∘ r'` and `t' ∘ r'` automorphisms of
`Spec(k')`.
-/
@[stacks 06E2] #check
  (existsAlgebraicallyClosedArrowLift :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
      (r : Points G.R.left),
      ∃ (k' : Type u) (_ : Field k') (ι : k →+* k') (_ : IsAlgClosed k'),
        let g := G.fieldRestrictionOfHom (IsOnField.objectSpaceIso G σ) ι
        let G' := G.pullback g
        let φ := G.pullbackHom g
        ∃ (r' : G'.U ⟶ G'.R),
          Points.map φ.arrow.left
              (Points.mk (FieldValuedPoint.of k'
                (Spec.map (CommRingCat.ofHom ι) ≫ σ) r'.left)) = r ∧
            IsIso (r' ≫ G'.s) ∧ IsIso (r' ≫ G'.t))
