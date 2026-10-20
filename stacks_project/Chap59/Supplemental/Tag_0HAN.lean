/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.LinearMap.Frobenius.BaseChange
import StacksCheckRecall

@[expose] public section

universe u u' v

/- Lemma [Stacks 0HAN] In the situation of lemma-F-1, if `k'/k` is an extension of
algebraically closed fields, `V' = k' ⊗[k] V`, and `F'` is the induced Frobenius-semilinear
endomorphism, then the canonical `ZMod p`-linear map `Ker(F - 1) → Ker(F' - 1)` sending `v`
to `1 ⊗ₜ v` is bijective. -/
@[stacks 0HAN] #check (LinearMap.Frobenius.subIdKerBaseChange_bijective :
  ∀ {k : Type u} {V : Type v} {p : ℕ}
    [Field k] [IsAlgClosed k] [Fact p.Prime] [CharP k p]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (k' : Type u') [Field k'] [IsAlgClosed k'] [Algebra k k'] [CharP k' p]
    (F : V →ₛₗ[_root_.frobenius k p] V),
    Function.Bijective (LinearMap.Frobenius.subIdKerBaseChange k' F))
