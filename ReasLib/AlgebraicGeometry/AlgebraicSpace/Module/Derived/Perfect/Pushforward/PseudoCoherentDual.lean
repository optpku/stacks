/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-! # Pseudo-coherent duals of relatively perfect derived pushforwards -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- For a proper flat finitely presented morphism with quasi-compact quasi-separated
target, the derived pushforward of derived sheaf Hom from a pseudo-coherent complex
to a relatively perfect complex is the dual of a pseudo-coherent complex. The same
pseudo-coherent complex gives this description after every cartesian base change. -/
theorem exists_pseudoCoherent_dual {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K) :
    ∃ L : ModuleDerived Y,
      IsPseudoCoherent Y L ∧
        IsIsomorphic ((Modules.moduleDerivedPushforward f).obj (InternalHom.obj K E))
          (InternalHom.obj L (structureSheafDerived Y)) ∧
        ∀ {X' Y' : AlgebraicSpace S}
          (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
          IsPullback g' f' f g →
            IsIsomorphic
              ((Modules.moduleDerivedPushforward f').obj
                (InternalHom.obj ((pullback g').obj K) ((pullback g').obj E)))
              (InternalHom.obj ((pullback g).obj L) (structureSheafDerived Y')) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
