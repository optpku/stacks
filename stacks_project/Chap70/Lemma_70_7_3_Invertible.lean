/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Invertible modules over inverse limits of algebraic spaces

Invertible modules descend along directed inverse limits of quasi-compact,
quasi-separated algebraic spaces with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Limit.Invertible

/-- An invertible module on a directed inverse limit of quasi-compact, quasi-separated
algebraic spaces with affine transition maps descends to an invertible module at some
stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (ℒ : c.pt.Modules) [isInvertibleObject ℒ] :
    ∃ (i : I) (ℒi : (D.obj i).Modules),
      isInvertibleObject ℒi ∧
        Nonempty ((Modules.pullback (c.π.app i)).obj ℒi ≅ ℒ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Limit.Invertible
