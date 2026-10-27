/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteType

/-!
# Universal purity of modules with proper support

A finite type quasi-coherent module is universally pure relative to the base
whenever its scheme-theoretic support is proper, and in particular whenever the
morphism itself is proper.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A finite type quasi-coherent module whose scheme-theoretic support is proper
over the base is universally pure relative to the base. -/
theorem isUniversallyPureOver_of_hasProperSupportOver
    (f : X ⟶ Y) [FiniteType f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType]
    [Proper ((schemeTheoreticSupport F).ι ≫ f)] :
    F.IsUniversallyPureOver f :=
  sorry

/-- A finite type quasi-coherent module on the source of a proper morphism is
universally pure relative to the target. -/
theorem isUniversallyPureOver_of_isProper
    (f : X ⟶ Y) [Proper f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf of the source of a proper morphism is universally pure
relative to the target. -/
theorem isUniversallyPureOver_of_isProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Decent f] :
    Modules.IsUniversallyPureOver
      (SheafOfModules.unit (structureSheaf X) : X.Modules) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
