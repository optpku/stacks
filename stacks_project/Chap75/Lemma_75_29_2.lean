module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

/-!
# Eventual Hom-vanishing after upper truncation

On a quasi-compact quasi-separated algebraic space, morphisms out of a perfect object of
`D(𝒪_X)` into an object of `D_QCoh(𝒪_X)` vanish in sufficiently negative shifts if and only
if the same holds after applying `t.truncLE a` to the target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.29.2: Let `S` be a scheme and let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `P` be perfect in `D(𝒪_X)`, let `E` be in `D_QCoh(𝒪_X)`,
and let `a : ℤ`. Then `Hom(P⟦-i⟧, E)` vanishes for all `i ≪ 0` if and only if
`Hom(P⟦-i⟧, (t.truncLE a).obj E)` vanishes for all `i ≪ 0`. -/
@[stacks 0GFG]
theorem extSubsingletonEventually_iff_truncLE {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (E : DerivedQCoh X) (a : ℤ) :
    (∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
      ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
        Subsingleton (Ext⁽i⁾(P, (t.truncLE a).obj E.obj)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
