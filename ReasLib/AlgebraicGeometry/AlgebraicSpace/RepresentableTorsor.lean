/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor

/-!
# Sheaf-theoretic fppf torsors for group algebraic spaces

For a group algebraic space over a scheme, fppf-cover-local triviality of a
pseudo-torsor is equivalent to simple transitivity and fppf-local nonemptiness
of its functor of points.
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

/-- Simple transitivity and fppf-local nonemptiness of the functor of points
give a sheaf torsor. -/
public def IsSheafTorsor.of (hX : Mod.IsPseudoTorsor X)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (terminal.from X.X.left.functorOfPoints)) :
    IsSheafTorsor G X where
  isPseudoTorsor := hX
  isLocallyNonempty := hsurj

/-- Sheaf torsorhood consists of simple transitivity and fppf-local
nonemptiness of the functor of points. -/
public theorem isSheafTorsor_iff :
    IsSheafTorsor G X ↔
      Mod.IsPseudoTorsor X ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (terminal.from X.X.left.functorOfPoints) := sorry

namespace IsStandardTorsor

/-- An fppf `G`-torsor is exactly a pseudo-torsor whose functor of points is
locally nonempty on `(Sch/S)_fppf`. -/
public theorem iff_isLocallySurjective :
    IsStandardTorsor G X .fppf ↔
      Mod.IsPseudoTorsor X ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (terminal.from X.X.left.functorOfPoints) := sorry

end IsStandardTorsor

/-- Fppf-cover-local torsorhood is equivalent to sheaf torsorhood on
`(Sch/S)_fppf`. -/
public theorem isStandardTorsor_iff_isSheafTorsor :
    IsStandardTorsor G X .fppf ↔ IsSheafTorsor G X := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
