/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.QuasiIso.Termwise
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
public import Mathlib.Algebra.Homology.ModelCategory.Lifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting from bounded-above projective cochain complexes

This is the projective dual of `InjectiveResolution.Lifting`.  It exposes homotopy and strict
lifts directly from a `ProjectiveMinus` source, so consumers do not reconstruct K-projectivity,
kernel acyclicity, or the cochain obstruction argument.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace ProjectiveMinus

/-- A map from a bounded-above complex of projectives lifts through a quasi-isomorphism up to
homotopy. -/
@[stacks 0649]
theorem exists_homotopy_lift
    (P : ProjectiveMinus A) {K L : CochainComplex A ℤ}
    (f : L ⟶ K) [QuasiIso f] (g : (P : CochainComplex A ℤ) ⟶ K) :
    ∃ h : (P : CochainComplex A ℤ) ⟶ L, Nonempty (Homotopy (h ≫ f) g) := sorry

/-- If the quasi-isomorphism is epimorphic in every degree, a map from a bounded-above complex
of projectives admits a strictly commuting lift. -/
@[stacks 0649]
theorem exists_lift_of_termwiseEpi
    (P : ProjectiveMinus A) {K L : CochainComplex A ℤ}
    (f : L ⟶ K) [QuasiIso f] (g : (P : CochainComplex A ℤ) ⟶ K)
    (hepi : ∀ n : ℤ, Epi (f.f n)) :
    ∃ h : (P : CochainComplex A ℤ) ⟶ L, h ≫ f = g := sorry

end ProjectiveMinus

end CochainComplex
