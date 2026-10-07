module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.IrreducibleComponents

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 29.54.6

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible components.
The coproduct of the normalizations of the reduced irreducible-component subschemes of `X` is
the normalization of `X`.
-/
@[stacks 0CDV] #check
  (AlgebraicGeometry.Scheme.normalizationIsoCoproductIrreducibleComponentNormalizations :
    ∀ (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X],
      let componentScheme : irreducibleComponents X → Scheme.{u} :=
        X.irreducibleComponentSubscheme
      ∃ e :
          (∐ fun Z : irreducibleComponents X ↦
              (componentScheme Z).normalization) ≅ X.normalization,
        Limits.Sigma.desc (fun Z : irreducibleComponents X ↦
            (componentScheme Z).normalizationTo ≫
              X.irreducibleComponentSubschemeι Z) =
          e.hom ≫ X.normalizationTo)

end AlgebraicGeometry.Scheme
