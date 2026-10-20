/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsUniversallyPureAlong

/-- A finite-type quasicoherent module is universally pure along a fibre if and only if
every pullback along a pointed morphism is pure along the selected fibre. -/
theorem iff_forall_pointedBaseChange {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    F.IsUniversallyPureAlong f s ↔
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S'), g s' = s →
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
          (pullback.snd f g) s' := sorry

end AlgebraicGeometry.Scheme.Modules.IsUniversallyPureAlong

namespace AlgebraicGeometry.Scheme.Modules.IsUniversallyPureOver

/-- A finite-type quasicoherent module is universally pure over its base if and only if
every base change is pure over the new base. -/
theorem iff_forall_baseChange {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f ↔
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureOver
          (pullback.snd f g) := sorry

end AlgebraicGeometry.Scheme.Modules.IsUniversallyPureOver

namespace AlgebraicGeometry.Scheme.Modules.IsPureAlong

/-- Purity along a fibre is preserved by a pointed base change that is quasi-finite at
the selected point. -/
theorem pullback_of_quasiFiniteAt {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S') (hpoint : g s' = s)
    (hquasi : Hom.FiniteType.QuasiFiniteAt g s')
    (hpure : F.IsPureAlong f s) :
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
      (pullback.snd f g) s' := sorry

end AlgebraicGeometry.Scheme.Modules.IsPureAlong
