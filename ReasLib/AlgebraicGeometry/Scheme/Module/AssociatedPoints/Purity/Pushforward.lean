/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteType.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite type quasicoherent module on a closed subscheme is pure along a fibre if and
only if its pushforward is pure along that fibre. -/
@[stacks 05K1]
theorem isPureAlong_pushforward_iff_of_isClosedImmersion
    {X Z S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Z.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S) :
    F.IsPureAlong (i ≫ f) s ↔
      ((Scheme.Modules.pushforward i).obj F).IsPureAlong f s := sorry

/-- A finite type quasicoherent module on a closed subscheme is universally pure along a
fibre if and only if its pushforward is universally pure along that fibre. -/
@[stacks 05K1]
theorem isUniversallyPureAlong_pushforward_iff_of_isClosedImmersion
    {X Z S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Z.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S) :
    F.IsUniversallyPureAlong (i ≫ f) s ↔
      ((Scheme.Modules.pushforward i).obj F).IsUniversallyPureAlong f s := sorry

end AlgebraicGeometry.Scheme.Modules
