/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Surjectivity
import StacksCheckRecall

/-!
# Lemma 77.9.3

In Situation 77.7.1, if `f` is locally of finite presentation, `𝒢` is of finite
type, and the support of `𝒢` is proper over `B`, then `F_surj` is the algebraic
space `surjectivityOpenSubspace f u`, and `F_surj ⟶ B` is an open immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 77.9.3. Surjectivity after base change is represented by the open subspace
complementary to the image of the cokernel support. -/
@[stacks 09TP] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.factors_surjectivityOpenSubspace_iff :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)
      [𝒢.IsFiniteType] [LocallyOfFinitePresentation f]
      [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
      {T : Over S} (a : ofOver T ⟶ B),
      (∃ ℓ : ofOver T ⟶ (surjectivityOpenSubspace f u).X,
          ℓ ≫ (surjectivityOpenSubspace f u).ι = a) ↔
        Epi (baseChangeMap f a u))

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)
variable [𝒢.IsFiniteType] [LocallyOfFinitePresentation f]
variable [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]

#check
  (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.isOpenImmersion
    (surjectivityOpenSubspace f u) : IsOpenImmersion (surjectivityOpenSubspace f u).ι)
