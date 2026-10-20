module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
import StacksCheckRecall

/-!
# Absolute normalization morphisms of algebraic spaces

The reusable construction and its properties are provided by the absolute
normalization owner; this file is the source-facing, tagged bridge.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

export AlgebraicGeometry.Scheme.Normalization (overNormalization overNormalizationTo)

/- Lemma 67.49.5 (1): the normality assertion in source clause (1). -/
@[stacks 07U4]
#check
  (AlgebraicGeometry.AlgebraicSpace.instIsNormal_normalization :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [HasFiniteIrreducibleComponentsOnCompactOpens X],
      IsNormal X.normalization)

/- Lemma 67.49.5 (2): the integrality assertion in source clause (1). -/
@[stacks 07U4]
#check
  (AlgebraicGeometry.AlgebraicSpace.instIsIntegralHom_normalizationTo :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [HasFiniteIrreducibleComponentsOnCompactOpens X],
      IsIntegralHom X.normalizationTo)

/- Lemma 67.49.5 (3): agreement with scheme normalization. -/
@[stacks 07U4]
#check
  (AlgebraicGeometry.AlgebraicSpace.Normalization.ofOverIso :
    ∀ {S : Scheme.{u}} (T : Over S)
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left],
      ∃! e : (ofOver T).normalization ≅
          AlgebraicGeometry.AlgebraicSpace.ofOverSchemeNormalization T,
        e.hom ≫ AlgebraicGeometry.AlgebraicSpace.ofOverSchemeNormalizationTo T =
          (ofOver T).normalizationTo)

/- Lemma 67.49.5 (4): the unique induced normalization map. -/
@[stacks 07U4]
#check
  (AlgebraicGeometry.AlgebraicSpace.Normalization.existsUnique_map :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [HasFiniteIrreducibleComponentsOnCompactOpens X]
      [HasFiniteIrreducibleComponentsOnCompactOpens Y] (f : X ⟶ Y),
      mapsCodimZero f →
        ∃! g : X.normalization ⟶ Y.normalization,
          g ≫ Y.normalizationTo = X.normalizationTo ≫ f)

/- Lemma 67.49.5 (5): compatibility with smooth base change. -/
@[stacks 07U4]
#check
  (AlgebraicGeometry.AlgebraicSpace.Normalization.existsUnique_pullbackIso_of_smooth_with_mapsTo :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Smooth f] [HasFiniteIrreducibleComponentsOnCompactOpens Y],
      -- Local instance justification (proof-local temporary data): the finite-component property derived from smoothness is needed only to form X.normalization in this dependent conclusion.
      letI : HasFiniteIrreducibleComponentsOnCompactOpens X :=
        HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth f
      mapsCodimZero f ∧ ∃! e : X.normalization ≅ pullback Y.normalizationTo f,
        e.hom ≫ pullback.snd Y.normalizationTo f = X.normalizationTo)

end AlgebraicGeometry.AlgebraicSpace
