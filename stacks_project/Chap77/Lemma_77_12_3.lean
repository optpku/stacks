/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Lemma_77_12_3_Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

universe u

/- Lemma 77.12.3 (1): in Situation 77.12.1, with `K` as in Lemma 77.12.2, for every
perfect object `E` of `D(𝒪_X)` the complex `M = RΓ(X, K ⊗ᴸ E)` is perfect in `D(A)`. -/
@[stacks 0CX6] #check globalSectionsTensor_isPerfect

/- Lemma 77.12.3 (2): there is a canonical isomorphism
`RΓ(X_n, ℱ n ⊗ᴸ E|_{X_n}) = M ⊗ᴸ_A A_n` in `D(A_n)`, where `E|_{X_n}` denotes derived
pullback of `E` to `X_n`. -/
@[stacks 0CX6] #check globalSectionsTensorBaseChangeMap_isIso

/- Lemma 77.12.3 (3): in Situation 77.12.1, with `K` as in Lemma 77.12.2, for every
perfect object `E` of `D(𝒪_X)` the complex `N = RHom_X(E, K)` is perfect in `D(A)`. -/
@[stacks 0CX6] #check globalHom_isPerfect

/- Lemma 77.12.3 (4): there is a canonical isomorphism
`RHom_{X_n}(E|_{X_n}, ℱ n) = N ⊗ᴸ_A A_n` in `D(A_n)`, where `E|_{X_n}` denotes derived
pullback of `E` to `X_n`. -/
@[stacks 0CX6] #check globalHomBaseChangeMap_isIso
