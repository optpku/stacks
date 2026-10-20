module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RegularAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Resolution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.NormalizedSequence

/-!
# Lipman's criterion for algebraic surfaces

For a two-dimensional integral Noetherian algebraic space, existence of a regular
alteration is equivalent to existence of a resolution of singularities, to a
resolution by normalized blowups, and to finiteness of the normalization together
with finitely many non-regular points whose henselian local rings have normal
adic completions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y]

/-- The normalization of a Noetherian integral algebraic space is finite, has finitely many
non-regular points, and the maximal-ideal adic completions of its henselian local rings at those
points are normal. -/
def hasFiniteNormalizationNormalCompletions : Prop :=
  IsFinite Y.normalizationTo ∧
    Set.Finite (setOf fun (y : Points Y.normalization) ↦ ¬ RegularAt Y.normalization y) ∧
      ∀ (y : Points Y.normalization), ¬ RegularAt Y.normalization y →
        IsNormalRing
          (AdicCompletion (maximalIdeal (henselianLocalRing Y.normalization y))
            (henselianLocalRing Y.normalization y))

/-- `hasFiniteNormalizationNormalCompletions` unpacks as finiteness of the normalization morphism,
finiteness of the non-regular locus of the normalization, and normality of the henselian
completions at those points. -/
theorem hasFiniteNormalizationNormalCompletions_iff :
    hasFiniteNormalizationNormalCompletions Y ↔
      IsFinite Y.normalizationTo ∧
        Set.Finite (setOf fun (y : Points Y.normalization) ↦ ¬ RegularAt Y.normalization y) ∧
          ∀ (y : Points Y.normalization), ¬ RegularAt Y.normalization y →
            IsNormalRing
              (AdicCompletion (maximalIdeal (henselianLocalRing Y.normalization y))
                (henselianLocalRing Y.normalization y)) :=
  Iff.rfl

/-- Let `S` be a scheme. Let `Y` be a two-dimensional integral Noetherian
algebraic space over `S`. The following are equivalent: there exists an alteration `X ⟶ Y`
with `X` regular, there exists a resolution of singularities of `Y`, `Y` has a resolution of
singularities by normalized blowups, the normalization `Y.normalizationTo` is finite,
`Y.normalization` has finitely many singular points, and for each such point the completion of
the henselian local ring `henselianLocalRing Y.normalization y` is normal. -/
@[stacks 0BHY]
theorem regularAlteration_tfae (h_dim : dimension Y = 2) :
    List.TFAE
      [ ∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
          IsAlteration f ∧ IsRegular X
      , ∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y), IsResolution f
      , HasResolutionByNormalizedBlowups Y h_dim
      , hasFiniteNormalizationNormalCompletions Y ] :=
  sorry

/-- For a two-dimensional integral Noetherian algebraic space, a regular alteration exists exactly
when a resolution of singularities exists. -/
theorem regularAlteration_iff_resolution (h_dim : dimension Y = 2) :
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      ∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y), IsResolution f :=
  (regularAlteration_tfae Y h_dim).out 0 1

/-- For a two-dimensional integral Noetherian algebraic space, a regular alteration exists exactly
when a resolution by normalized blowups exists. -/
theorem regularAlteration_iff_normalizedBlowups (h_dim : dimension Y = 2) :
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      HasResolutionByNormalizedBlowups Y h_dim :=
  (regularAlteration_tfae Y h_dim).out 0 2

/-- For a two-dimensional integral Noetherian algebraic space, a regular alteration exists exactly
when the normalization is finite, has finitely many non-regular points, and has normal henselian
completions at those points. -/
theorem regularAlteration_iff_finiteNormalization_normalCompletions
    (h_dim : dimension Y = 2) :
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      hasFiniteNormalizationNormalCompletions Y :=
  (regularAlteration_tfae Y h_dim).out 0 3

end AlgebraicGeometry.AlgebraicSpace
