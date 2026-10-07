module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Finite locally free modules over inverse limits of algebraic spaces

Finite locally free modules descend along directed inverse limits of quasi-compact,
quasi-separated algebraic spaces with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FiniteLocallyFree

/-- A finite locally free module on a directed inverse limit of quasi-compact,
quasi-separated algebraic spaces with affine transition maps descends to a finite
locally free module at some stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (ℱ : c.pt.Modules) [ℱ.IsFiniteLocallyFree] :
    ∃ (i : I) (ℱi : (D.obj i).Modules),
      ℱi.IsFiniteLocallyFree ∧
        Nonempty ((Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FiniteLocallyFree
