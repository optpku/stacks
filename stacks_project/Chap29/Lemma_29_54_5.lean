module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 29.54.5 (1)

For a scheme whose quasi-compact opens have finitely many irreducible components, its
normalization is covered by pairwise disjoint normal integral open subschemes.
-/
@[stacks 035Q] #check
  (Normalization.cover :
    ∀ (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X],
      X.normalization.HasPairwiseDisjointOpenCoverByNormalIntegral)

variable (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]

/- Lemma 29.54.5 (2a): the normalization morphism is integral. -/
@[stacks 035Q] #check
  (Hom.instIsIntegralHomFromNormalization (genericPointSpectrumCoproductTo X) :
    IsIntegralHom X.normalizationTo)

/- Lemma 29.54.5 (2b): the normalization morphism is surjective. -/
@[stacks 035Q] #check
  (Normalization.surjective :
    ∀ (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X],
      Surjective X.normalizationTo)

/- Lemma 29.54.5 (2c): the normalization morphism bijects generic points. -/
@[stacks 035Q] #check
  (Normalization.bijOn_genericPoints :
    ∀ (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X],
      Set.BijOn X.normalizationTo (genericPoints X.normalization) (genericPoints X))

/- Lemma 29.54.5 (3): birational integral morphisms admit a normalization factorization. -/
@[stacks 035Q] #check
  (Normalization.exists_factorization :
    ∀ (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
      {X' : Scheme.{u}} (α : X' ⟶ X) [IsIntegralHom α],
      α.IsBirationalOnCompactOpens →
        ∃ hX' : HasFiniteIrreducibleComponentsOnCompactOpens X',
          -- Local instance justification (proof-local temporary data): the existential
          -- finite-component proof is installed only to form the intermediate
          -- normalization in this dependent conclusion.
          letI : HasFiniteIrreducibleComponentsOnCompactOpens X' := hX'
          ∃ β : X.normalization ⟶ X',
            β ≫ α = X.normalizationTo ∧
              ∃ e : X.normalization ≅ X'.normalization,
                β = e.hom ≫ X'.normalizationTo)

/- Lemma 29.54.5 (4): maps from normal schemes lift uniquely through normalization. -/
@[stacks 035Q] #check
  (Normalization.existsUnique_lift_of_isNormal :
    ∀ (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
      {Z : Scheme.{u}} (g : Z ⟶ X), Z.isNormal →
      Set.MapsTo g (genericPoints Z) (genericPoints X) →
        ∃! h : Z ⟶ X.normalization, h ≫ X.normalizationTo = g)

end AlgebraicGeometry.Scheme
