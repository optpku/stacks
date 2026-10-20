/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Functor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.FiniteProjective
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Morphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Monoidal

/-!
# Associated module sheaves

This is the stable import surface for modules over global scalars and their associated module
sheaves. The leaf files separate the functor, adjunction, base-change and morphism comparison,
finite-projective restriction, quasi-coherent lift, tensor-presheaf model, free presentations,
stalks, and local properties.
-/

@[expose] public section
