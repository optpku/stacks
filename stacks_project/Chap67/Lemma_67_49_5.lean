module

public import stacks_project.Chap67.Lemma_67_49_5_Normalization

/-!
# Absolute normalization morphisms of algebraic spaces

Lemma 67.49.5 constructs, for every algebraic space satisfying the equivalent
conditions of Lemma 67.49.1, a canonical absolute normalization morphism
`ν_X : X^ν ⟶ X`, and records its basic properties.

The five atomic declarations below represent four clauses in the source.
Atomic parts (1) and (2) split source clause (1) into normality and integrality;
atomic parts (3), (4), and (5) represent source clauses (2), (3), and (4).
Parenthesized suffixes in the labels enumerate declarations, not source clauses.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.49.5 (1): the normality assertion in source clause (1).
Let `S` be a scheme. For every algebraic space `X` over `S`
satisfying the equivalent conditions of Lemma 67.49.1, recorded as
`HasFiniteIrreducibleComponentsOnCompactOpens X`, the absolute normalization
`X.normalization` is a normal algebraic space. -/
@[stacks 07U4]
instance instIsNormal_normalization {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsNormal X.normalization :=
  sorry

/-- Lemma 67.49.5 (2): the integrality assertion in source clause (1).
Let `S` be a scheme. For every algebraic space `X` over `S`
satisfying the equivalent conditions of Lemma 67.49.1, recorded as
`HasFiniteIrreducibleComponentsOnCompactOpens X`, the canonical morphism
`X.normalizationTo` is integral. -/
@[stacks 07U4]
instance instIsIntegralHom_normalizationTo {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsIntegralHom X.normalizationTo :=
  sorry

namespace Normalization

/-- Lemma 67.49.5 (3): source clause (2), agreement with scheme normalization.
If `X` is representable by a scheme `T` over `S` whose
quasi-compact opens have finitely many irreducible components, then
`(ofOver T).normalizationTo` is uniquely isomorphic over `ofOver T` to the
scheme-level absolute normalization `ofOverSchemeNormalizationTo T`. -/
@[stacks 07U4]
theorem ofOverIso {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ∃! e : (ofOver T).normalization ≅ ofOverSchemeNormalization T,
      e.hom ≫ ofOverSchemeNormalizationTo T = (ofOver T).normalizationTo :=
  sorry

/-- Lemma 67.49.5 (4): source clause (3), the unique induced normalization map.
Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`
which both satisfy the equivalent conditions of Lemma 67.49.1, and suppose every
codimension-`0` point of `X` is mapped by `f` to a codimension-`0` point of `Y`.
Then there is a unique morphism `f^ν : X.normalization ⟶ Y.normalization` such
that `Y.normalizationTo ∘ f^ν = f ∘ X.normalizationTo`. -/
@[stacks 07U4]
theorem existsUnique_map {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] (f : X ⟶ Y)
    (hf : mapsCodimZero f) :
    ∃! g : X.normalization ⟶ Y.normalization,
      g ≫ Y.normalizationTo = X.normalizationTo ≫ f :=
  sorry

/-- Lemma 67.49.5 (5): source clause (4), compatibility with étale or smooth base change.
If `f : X ⟶ Y` is an étale or smooth morphism of algebraic
spaces and `Y` satisfies the equivalent conditions of Lemma 67.49.1, then the
hypotheses of source clause (3) hold via `HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth`
and `mapsCodimZero_of_smooth`, with étale included by `smooth_of_etale`, and
`f^ν` induces a unique isomorphism `X.normalization ≅ pullback Y.normalizationTo f`
over `X` whose second projection is `X.normalizationTo`. -/
@[stacks 07U4]
theorem existsUnique_pullbackIso_of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ∃! e : X.normalization ≅ pullback Y.normalizationTo f,
      e.hom ≫ pullback.snd Y.normalizationTo f = X.normalizationTo :=
  sorry

end Normalization

end AlgebraicGeometry.AlgebraicSpace
