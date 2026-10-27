/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation

/-! # Properties of the structure morphism of the stack of relatively perfect complexes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom renaming QuasiSeparated → StackQuasiSeparated,
  LocallyOfFinitePresentation → StackLocallyOfFinitePresentation
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a proper, flat morphism of finite presentation, the structure morphism
of the stack of relatively perfect complexes with vanishing negative fibre
self-Ext is quasi-separated. -/
instance instQuasiSeparated_toBase (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    StackQuasiSeparated (toBase f) := sorry

/-- For a proper, flat morphism of finite presentation, the structure morphism
of the stack of relatively perfect complexes with vanishing negative fibre
self-Ext is locally of finite presentation. -/
instance instLocallyOfFinitePresentation_toBase (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    StackLocallyOfFinitePresentation (toBase f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
