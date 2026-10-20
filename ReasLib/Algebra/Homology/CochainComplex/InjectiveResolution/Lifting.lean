/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.QuasiIso.Termwise
public import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded
public import Mathlib.Algebra.Homology.ModelCategory.Lifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting into bounded-below injective cochain complexes

This leaf combines the K-injective homotopy transport API with the termwise-monomorphic
strictification criterion.  Consumers can request the lift directly from an `InjectivePlus`
target without rebuilding K-injectivity, cokernel acyclicity, or obstruction data locally.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace InjectivePlus

/-- A map into a bounded-below complex of injectives lifts along a quasi-isomorphism up to
homotopy. -/
@[stacks 013P]
theorem exists_homotopy_lift
    (I : InjectivePlus A) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) [QuasiIso f] (g : K ⟶ I) :
    ∃ h : L ⟶ I, Nonempty (Homotopy (f ≫ h) g) := sorry

/-- If the quasi-isomorphism is monomorphic in every degree, a map into a bounded-below complex
of injectives admits a strictly commuting lift. -/
@[stacks 013P]
theorem exists_lift_of_termwiseMono
    (I : InjectivePlus A) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) [QuasiIso f] (g : K ⟶ I)
    (hmono : ∀ n : ℤ, Mono (f.f n)) :
    ∃ h : L ⟶ I, f ≫ h = g := sorry

end InjectivePlus

end CochainComplex
