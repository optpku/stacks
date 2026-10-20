/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation

@[expose] public section

universe u v w

namespace RingHom.FinitePresentation

/-- A ring homomorphism is of finite presentation together with a finitely presented module
over a localization of its codomain. -/
def withModuleOverLocalization {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (S : Submonoid B) (N : Type w) [AddCommGroup N]
    [Module (Localization S) N] : Prop :=
  f.FinitePresentation ∧ Module.FinitePresentation (Localization S) N

end RingHom.FinitePresentation
