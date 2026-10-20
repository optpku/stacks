/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Genus of a smooth projective curve

This file defines the genus as the dimension of the first cohomology of the
structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- The genus of a smooth projective geometrically irreducible curve is the dimension of the
first cohomology of its structure sheaf. -/
noncomputable def genus
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] : ℕ :=
  Scheme.Hom.cohomologyFinrank X.hom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1

/-- The genus is the degree-one cohomology dimension of the structure sheaf. -/
theorem genus_def
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] :
    genus X = Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

/-- The genus of a smooth projective curve over an algebraically closed field is the
dimension of the degree-one cohomology of its structure sheaf. -/
noncomputable def genusOfAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Curve X]
    [Projective X.hom] [Smooth X.hom] : ℕ :=
  Scheme.Hom.cohomologyFinrank X.hom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1

/-- Over an algebraically closed field, the genus equals the degree-one structure-sheaf
cohomology dimension. -/
theorem genusOfAlgClosed_def
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Curve X]
    [Projective X.hom] [Smooth X.hom] :
    genusOfAlgClosed X = Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

/-- For a geometrically irreducible curve over an algebraically closed field, the two
cohomological genus definitions agree. -/
theorem genusOfAlgClosed_eq_genus
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Curve X]
    [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] :
    genusOfAlgClosed X = genus X := sorry

end AlgebraicGeometry.Curve
