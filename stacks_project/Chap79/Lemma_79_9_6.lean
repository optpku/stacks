module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.FieldPoints

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace

universe u

/- Lemma 79.9.6: in Situation 79.9.2, every point `r` of `|R|` lifts after restriction
along some algebraically closed extension `k'/k` to a morphism `r' : Spec(k') ⟶ R'`
that maps to `r` under `R' ⟶ R`, with `s' ∘ r'` and `t' ∘ r'` automorphisms of
`Spec(k')`.
-/
@[stacks 06E2] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.existsAlgebraicallyClosedArrowLift :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
      (r : Points G.R.left),
      ∃ (k' : Type u) (_ : Field k') (ι : k →+* k') (_ : IsAlgClosed k'),
        let g := G.fieldRestrictionOfHom (IsOnField.objectSpaceIso G σ) ι
        let G' := G.pullback g
        let φ := G.pullbackHom g
        ∃ (r' : G'.U.left ⟶ G'.R.left),
          Points.map φ.arrow.left
              (Points.mk (FieldValuedPoint.of k'
                (Spec.map (CommRingCat.ofHom ι) ≫ σ) r')) = r ∧
            IsIso (r' ≫ G'.s.left) ∧ IsIso (r' ≫ G'.t.left))
