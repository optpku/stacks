/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Injectivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.2.11: let `S` be a scheme, let `X` be an algebraic space over `S`,
and let `φ : F ⟶ G` be a morphism of quasi-coherent `𝒪_X`-modules. If for every
point `x` of `|X|` either the étale stalk map `F_{x̄} ⟶ G_{x̄}` is injective for
every geometric point `x̄` lying over `x`, or `x ∉ F.weakAss`, then `φ` is a
monomorphism. -/
@[stacks 0CUR] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mono_of_stalkwise_injective_or_not_mem_weakAss :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G),
      (∀ x : Points X,
        (∀ xbar : GeometricPoint X,
          xbar.liesOver x → Function.Injective (stalkModuleCatMap xbar φ)) ∨
          x ∉ F.weakAss) → Mono φ)
