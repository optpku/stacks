module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal
public import stacks_project.Chap78.Definition_78_9_3_Torsor

/-!
# Sheaf-theoretic fppf torsors for group algebraic spaces

This module packages the Cohomology on Sites 21.4.1 condition for a group
algebraic space over a scheme `S`, and compares it with the fppf space-torsor
`IsStandardTorsor G X .fppf` of Definition 78.9.3.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

variable {S : Scheme.{u}} (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
  (X : Action G)

/-- The action is simply transitive and the functor of points of `X` is locally
nonempty on `(Sch/S)_fppf`. -/
public structure IsSheafTorsor : Prop where
  /-- The geometric action is a pseudo-torsor. -/
  isPseudoTorsor : Mod.IsPseudoTorsor X
  /-- The functor of points is locally nonempty for the fppf topology on `Over S`. -/
  isLocallyNonempty :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (terminal.from X.X.left.functorOfPoints)

/-- Constructs the 21.4.1 packaging from simple transitivity and fppf-local
nonemptiness of the functor of points. -/
public def IsSheafTorsor.of (hX : Mod.IsPseudoTorsor X)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (terminal.from X.X.left.functorOfPoints)) :
    IsSheafTorsor G X where
  isPseudoTorsor := hX
  isLocallyNonempty := hsurj

/-- The 21.4.1 packaging consists of simple transitivity and fppf-local
nonemptiness of the functor of points. -/
public theorem isSheafTorsor_iff :
    IsSheafTorsor G X ↔
      Mod.IsPseudoTorsor X ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (terminal.from X.X.left.functorOfPoints) := sorry

namespace IsStandardTorsor

/-- An fppf `G`-torsor in the sense of Definition 78.9.3 is exactly a
pseudo-torsor whose functor of points is locally nonempty on `(Sch/S)_fppf`. -/
public theorem iff_isLocallySurjective :
    IsStandardTorsor G X .fppf ↔
      Mod.IsPseudoTorsor X ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (terminal.from X.X.left.functorOfPoints) := sorry

end IsStandardTorsor

/-- An fppf `G`-torsor in the sense of Definition 78.9.3 is exactly a `G`-torsor
on `(Sch/S)_fppf` in the sense of Definition 21.4.1. -/
public theorem isStandardTorsor_iff_isSheafTorsor :
    IsStandardTorsor G X .fppf ↔ IsSheafTorsor G X := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
