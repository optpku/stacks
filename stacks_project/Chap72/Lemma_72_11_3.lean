module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced.Etale
import StacksCheckRecall

/-!
# Geometric reducedness of algebraic spaces via étale scheme charts

An algebraic space over a field is geometrically reduced if and only if some,
equivalently any, étale morphism from a scheme is geometrically reduced on the
source, with surjectivity required only for the existence of one such chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat

noncomputable section

universe u

/- Lemma 72.11.3: let `k` be a field and let `X` be an algebraic space over `k`.
The following are equivalent: `X` is geometrically reduced; there exists a
surjective étale morphism `U ⟶ X` with `U` a scheme such that `U` is
geometrically reduced; and every étale morphism `U ⟶ X` with `U` a scheme has
`U` geometrically reduced. -/
@[stacks 0DMS] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReduced_etale_tfae :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    List.TFAE
      [GeometricallyReduced X,
        ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
            AlgebraicSpace.Surjective a ∧ SchemeOverField.geometricallyReduced U,
        ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
            SchemeOverField.geometricallyReduced U])

/- `X` is geometrically reduced if and only if some surjective étale morphism
from a scheme is geometrically reduced on the source. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReduced_iff_exists_surjective_etale :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyReduced X ↔
      ∃ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          AlgebraicSpace.Surjective a ∧ SchemeOverField.geometricallyReduced U)

/- `X` is geometrically reduced if and only if every étale morphism from a
scheme is geometrically reduced on the source. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReduced_iff_forall_etale :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyReduced X ↔
      ∀ (U : Over (Spec (of k))) (a : ofOver U ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          SchemeOverField.geometricallyReduced U)
