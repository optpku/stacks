/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.RingTheory.Normal.Local
public import stacks_project.Chap66.Definition_66_25_2_RegularAt
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap72.Definition_72_8_3_Alteration
public import stacks_project.Chap89.Definition_89_8_1_Resolution
public import stacks_project.Chap89.Definition_89_8_2_Sequence

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
  sorry

/-- Theorem 89.8.3: Let `S` be a scheme. Let `Y` be a two dimensional integral Noetherian
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
  sorry

/-- For a two-dimensional integral Noetherian algebraic space, a regular alteration exists exactly
when a resolution by normalized blowups exists. -/
theorem regularAlteration_iff_normalizedBlowups (h_dim : dimension Y = 2) :
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      HasResolutionByNormalizedBlowups Y h_dim :=
  sorry

/-- For a two-dimensional integral Noetherian algebraic space, a regular alteration exists exactly
when the normalization is finite, has finitely many non-regular points, and has normal henselian
completions at those points. -/
theorem regularAlteration_iff_finiteNormalization_normalCompletions
    (h_dim : dimension Y = 2) :
    (∃ (X : AlgebraicSpace S) (_ : IsIntegral X) (f : X ⟶ Y),
      IsAlteration f ∧ IsRegular X) ↔
      hasFiniteNormalizationNormalCompletions Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
