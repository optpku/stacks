/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.Geometric.Normal
public import ReasLib.RingTheory.FormalFiber.Geometric.Reduced
public import ReasLib.RingTheory.FormalFiber.Geometric.Regular

@[expose] public section

/-!
# Geometric properties of formal fibers

Compatibility aggregate for the three independent geometric field-algebra
properties and their formal-fiber permanence instances.
-/

#synth FieldAlgebraProperty.geometricallyReduced.EssFiniteTypeBaseChange
#synth FieldAlgebraProperty.geometricallyReduced.IsLocal
#synth FieldAlgebraProperty.geometricallyReduced.RegularFiberAscent
#synth FieldAlgebraProperty.geometricallyReduced.FaithfullyFlatDescent
#synth FieldAlgebraProperty.geometricallyReduced.SeparableExtension
#synth FieldAlgebraProperty.geometricallyNormal.EssFiniteTypeBaseChange
#synth FieldAlgebraProperty.geometricallyNormal.IsLocal
#synth FieldAlgebraProperty.geometricallyNormal.RegularFiberAscent
#synth FieldAlgebraProperty.geometricallyNormal.FaithfullyFlatDescent
#synth FieldAlgebraProperty.geometricallyNormal.SeparableExtension
#synth FieldAlgebraProperty.geometricallyRegular.EssFiniteTypeBaseChange
#synth FieldAlgebraProperty.geometricallyRegular.IsLocal
#synth FieldAlgebraProperty.geometricallyRegular.RegularFiberAscent
#synth FieldAlgebraProperty.geometricallyRegular.FaithfullyFlatDescent
#synth FieldAlgebraProperty.geometricallyRegular.SeparableExtension
