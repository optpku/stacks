module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Order.Filter.AtTopBot.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

/-!
# Eventual Hom-vanishing after truncation

On a quasi-compact quasi-separated algebraic space, morphisms out of negative shifts of a
perfect object of `D(𝒪_X)` into an object of `D_QCoh(𝒪_X)` vanish for large cohomological
degree if and only if the same vanishing holds after applying any lower truncation of the
target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a perfect derived module on a quasi-compact quasi-separated algebraic space, eventual
vanishing of morphisms out of negative shifts into a derived quasicoherent object is
equivalent to eventual vanishing after any lower truncation of the target. -/
theorem homSubsingletonEventually_iff_truncGE {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (E : DerivedQCoh X) (a : ℤ) :
    (∀ᶠ i : ℤ in Filter.atTop, Subsingleton (P⟦-i⟧ ⟶ (inclusion X).obj E)) ↔
      ∀ᶠ i : ℤ in Filter.atTop,
        Subsingleton (P⟦-i⟧ ⟶ (t.truncGE a).obj ((inclusion X).obj E)) := sorry

/-- For a perfect derived module on a quasi-compact quasi-separated algebraic space, eventual
vanishing of Ext into a derived quasicoherent object is equivalent to eventual vanishing
after any lower truncation of the target. -/
theorem extSubsingletonEventually_iff_truncGE {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (E : DerivedQCoh X) (a : ℤ) :
    (∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, (inclusion X).obj E))) ↔
      ∀ᶠ i : ℤ in Filter.atTop,
        Subsingleton (Ext⁽i⁾(P, (t.truncGE a).obj ((inclusion X).obj E))) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
