module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Finite locally free modules over inverse limits of algebraic spaces

Finite locally free modules descend along directed inverse limits of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FiniteLocallyFree

/-- A finite locally free module on a directed inverse limit of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transition maps descends to a finite
locally free module at some stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    (ℱ : c.pt.Modules) [ℱ.IsFiniteLocallyFree] :
    ∃ (i : I) (ℱi : (D.obj i).Modules),
      ℱi.IsFiniteLocallyFree ∧
        Nonempty ((Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Limit.FiniteLocallyFree
