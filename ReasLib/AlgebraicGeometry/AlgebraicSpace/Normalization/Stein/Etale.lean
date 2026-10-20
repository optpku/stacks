/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedFibres
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced

/-!
# Finite étaleness of the Stein second factor

For a proper morphism of algebraic spaces that is of finite presentation, flat,
and has geometrically reduced fibres, the structure morphism of the relative
normalization is finite and étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The structure morphism of the relative normalization of a proper morphism of
algebraic spaces that is of finite presentation, flat, and has reduced geometric
fibres is finite. -/
instance instIsFiniteFromNormalizationOfFlatGeometricallyReduced
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f] [HasReducedGeometricFibres f] :
    IsFinite (fromNormalization f) := sorry

/-- The structure morphism of the relative normalization of a proper morphism of
algebraic spaces that is of finite presentation, flat, and has reduced geometric
fibres is étale. -/
instance instEtaleFromNormalizationOfFlatGeometricallyReduced
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f] [HasReducedGeometricFibres f] :
    Etale (fromNormalization f) := sorry

/-- If a proper morphism of algebraic spaces is of finite presentation, flat, and
the geometrically reduced fibre locus is all of `Points Y`, then the structure
morphism of the relative normalization is finite. -/
theorem isFinite_fromNormalization_of_geometricallyReducedFiberLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) :
    IsFinite (fromNormalization f) := sorry

/-- If a proper morphism of algebraic spaces is of finite presentation, flat, and
the geometrically reduced fibre locus is all of `Points Y`, then the structure
morphism of the relative normalization is étale. -/
theorem etale_fromNormalization_of_geometricallyReducedFiberLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) :
    Etale (fromNormalization f) := sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
