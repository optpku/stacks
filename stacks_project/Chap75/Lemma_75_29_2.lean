/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Truncation
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedExt

universe u

/- Lemma 75.29.2: Let `S` be a scheme and let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `P` be perfect in `D(𝒪_X)`, let `E` be in `D_QCoh(𝒪_X)`,
and let `a : ℤ`. Then `Hom(P⟦-i⟧, E)` vanishes for all `i ≪ 0` if and only if
`Hom(P⟦-i⟧, (t.truncLE a).obj E)` vanishes for all `i ≪ 0`. -/
@[stacks 0GFG] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.extSubsingletonEventually_iff_truncLE :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {P : ModuleDerived X},
      ModuleDerived.IsPerfect P → ∀ (E : DerivedQCoh X) (a : ℤ),
        (∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
            Subsingleton (Ext⁽i⁾(P, (t.truncLE a).obj E.obj)))
