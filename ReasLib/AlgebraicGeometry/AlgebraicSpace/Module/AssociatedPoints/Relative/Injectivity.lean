/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- If a flat morphism of algebraic spaces over `Y` covers the relative associated points
of a finite-type quasi-coherent module that is flat over `Y`, and the source of the module
is locally of finite type over `Y`, then the canonical pullback-pushforward unit is a
monomorphism. -/
@[stacks 0CW6]
theorem unit_mono_of_subset_range {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [Flat g] [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType]
    (h_flat : flatOver F f)
    (hAss : relativeAssassin f F ⊆ Set.range (Points.map g)) :
    Mono ((pullbackPushforwardAdjunction g).unit.app F) :=
  sorry

/-- If a flat morphism of algebraic spaces over `Y` covers the relative associated points
of a finite-type quasi-coherent module that is flat over `Y`, and the source of the module
is locally of finite type over `Y`, then the canonical pullback-pushforward unit remains a
monomorphism after every algebraic-space base change to `Y`. -/
@[stacks 0CW6]
theorem unit_mono_afterBaseChange_of_subset_range {S : Scheme.{u}}
    {Y X X' : AlgebraicSpace S} (f : X ⟶ Y) (g : X' ⟶ X) [Flat g]
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_flat : flatOver F f)
    (hAss : relativeAssassin f F ⊆ Set.range (Points.map g))
    {Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    Mono ((pullbackPushforwardAdjunction (Limits.pullback.fst (Limits.pullback.fst f h) g)).unit.app
      ((pullback (Limits.pullback.fst f h)).obj F)) :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
