module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced.Etale
import StacksCheckRecall

/-!
# Geometric reducedness at a point of an algebraic space

An algebraic space over a field is geometrically reduced at a point if and only if
some, equivalently any, étale scheme neighbourhood of that point is geometrically
reduced at the source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat

noncomputable section

universe u

/- Lemma 72.11.2: let `k` be a field, let `X` be an algebraic space over `k`, and
let `x` be a point of `|X|`. The following are equivalent: `X` is geometrically
reduced at `x`; there exists an étale neighbourhood `(U, u) ⟶ (X, x)` with `U` a
scheme such that `U` is geometrically reduced at `u`; and every such étale
neighbourhood has `U` geometrically reduced at `u`. -/
@[stacks 0DMR] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_isGeometricallyReduced_tfae :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} (x : Points X),
    List.TFAE
      [GeometricallyReducedAt X x,
        ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
            Points.mapOfOver a u = x ∧ SchemeOverField.geometricallyReducedAt U u,
        ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
            Points.mapOfOver a u = x → SchemeOverField.geometricallyReducedAt U u])

/- `X` is geometrically reduced at `x` if and only if some étale scheme
neighbourhood of `x` is geometrically reduced at the source point. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.isGeometricallyReducedAt_iff_exists_etale :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} (x : Points X),
    GeometricallyReducedAt X x ↔
      ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          Points.mapOfOver a u = x ∧ SchemeOverField.geometricallyReducedAt U u)

/- `X` is geometrically reduced at `x` if and only if every étale scheme
neighbourhood of `x` is geometrically reduced at the source point. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.isGeometricallyReducedAt_iff_forall_etale :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} (x : Points X),
    GeometricallyReducedAt X x ↔
      ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          Points.mapOfOver a u = x → SchemeOverField.geometricallyReducedAt U u)
