/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.UniversallyClosed
import StacksCheckRecall

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

/- Lemma 67.48.9: let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact,
quasi-separated and universally closed morphism of algebraic spaces over `S`.
Then `f_* 𝒪_X` is integral over `𝒪_Y`. -/
@[stacks 0A0Q] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsIntegral_pushforwardStructureQcAlgebra :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f],
      QcAlgebraUnder.IsIntegral (pushforwardStructureQcAlgebra f))

/- In other words, the normalization of `Y` in `X` is the
factorization `X ⟶ relativeSpec (pushforwardStructureQcAlgebra f) ⟶ Y` of
Remark 67.20.9. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isNormalization_toPushforwardRelativeSpec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f],
      IsNormalization f (Hom.toPushforwardRelativeSpec f)
        (relativeSpecπ (pushforwardStructureQcAlgebra f)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsIso_integralClosureAlgebra_inclusion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f],
      IsIso (integralClosureAlgebra_inclusion f))
