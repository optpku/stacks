/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.EmbeddedSurface
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.15.6 (local erratum): for a Noetherian regular dimension-two scheme and a
closed subscheme with nowhere dense support whose one-dimensional irreducible components
have finite normalization, finitely many closed-point blowups make the inverse image an
effective Cartier divisor supported on a strict normal crossings divisor. The finiteness
and support corrections agree with the local erratum to Lemma 54.15.5. -/
@[stacks 0BIC]
#check
  (AlgebraicGeometry.Scheme.existsEffectiveCartierInverseImageWithStrictNormalCrossingsSupport :
    ∀ (X : Scheme.{u}) [IsNoetherian X] [Regular X],
      topologicalKrullDim X = 2 →
      ∀ (Z : X.IdealSheafData), interior (closure Z.supportSet) = ∅ →
      (∀ C : irreducibleComponents Z.subscheme,
        topologicalKrullDim (Z.subscheme.irreducibleComponentSubscheme C) = 1 →
          IsFinite (normalizationToOfIsNoetherian
            (Z.subscheme.irreducibleComponentSubscheme C))) →
      ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
        IsEffectiveCartierDivisor (Z.comap s.toSource).subschemeι ∧
          ∃ (h_noetherian : IsLocallyNoetherian Xn) (D : Xn.IdealSheafData),
            @IsStrictNormalCrossingsDivisor Xn h_noetherian D ∧
              (Z.comap s.toSource).supportSet ⊆ D.supportSet)

end AlgebraicGeometry.Scheme
