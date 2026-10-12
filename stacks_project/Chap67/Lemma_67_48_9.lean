/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_48_9_Integral
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Remark_67_20_9_Factorization
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Lemma_67_48_8_Normalization

/-!
# Integrality of `f_* 𝒪_X` for universally closed qcqs morphisms

If `f : X ⟶ Y` is a quasi-compact, quasi-separated and universally closed morphism
of algebraic spaces, then `f_* 𝒪_X` is integral over `𝒪_Y`, so the Remark 67.20.9
factorization through `relativeSpec (pushforwardStructureQcAlgebra f)` is a relative
normalization of `Y` in `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 67.48.9 (1): let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact,
quasi-separated and universally closed morphism of algebraic spaces over `S`.
Then `f_* 𝒪_X` is integral over `𝒪_Y`. -/
@[stacks 0A0Q]
instance instIsIntegral_pushforwardStructureQcAlgebra
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] :
    QcAlgebraUnder.IsIntegral (pushforwardStructureQcAlgebra f) :=
  sorry

/-- Lemma 67.48.9 (2): in other words, the normalization of `Y` in `X` is the
factorization `X ⟶ relativeSpec (pushforwardStructureQcAlgebra f) ⟶ Y` of
Remark 67.20.9. -/
@[stacks 0A0Q]
theorem isNormalization_toPushforwardRelativeSpec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] :
    IsNormalization f (toPushforwardRelativeSpec f)
      (relativeSpecπ (pushforwardStructureQcAlgebra f)) :=
  sorry

/-- If `f` is quasi-compact, quasi-separated and universally closed, then the
inclusion of the integral closure of `𝒪_Y` in `f_* 𝒪_X` is an isomorphism. -/
instance instIsIso_integralClosureAlgebra_inclusion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] :
    IsIso (integralClosureAlgebra_inclusion f) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
