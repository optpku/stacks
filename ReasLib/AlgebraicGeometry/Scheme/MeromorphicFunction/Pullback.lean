/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.Integral
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints.GenericPoints
import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints.GenericPoints
import ReasLib.AlgebraicGeometry.Scheme.Module.RegularSection
import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ZeroDivisor
import ReasLib.RingTheory.Localization.TotalQuotient

/-!
# Pullbacks of meromorphic functions on schemes

This file gives geometric conditions ensuring that a scheme morphism preserves regular
meromorphic denominators under pullback.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom.MeromorphicFunction

/-- A scheme morphism preserves regular meromorphic denominators if it maps every weakly
associated point of the source to a generic point of the target. -/
theorem pullbackDefined_of_weakAss_mapsTo_genericPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hweak : Set.MapsTo f.base X.weakAss (genericPoints Y)) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom := sorry

/-- A dominant morphism between integral schemes preserves regular meromorphic denominators. -/
theorem pullbackDefined_of_isIntegral_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom := sorry

/-- A morphism from an integral scheme preserves regular meromorphic denominators if the source's
generic point maps to a generic point of the target. -/
theorem pullbackDefined_of_isIntegral_of_map_genericPoint_mem_genericPoints
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    (hgeneric : f.base (genericPoint X) ∈ genericPoints Y) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom := sorry

/-- A morphism from a reduced scheme preserves regular meromorphic denominators if it maps the
source's generic points to generic points of the target. -/
theorem pullbackDefined_of_genericPoints_mapsTo_of_isReduced
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y)
    (hgeneric : Set.MapsTo f.base (genericPoints X) (genericPoints Y)) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom := sorry

/-- A morphism from a locally Noetherian scheme preserves regular meromorphic denominators if it
maps the source's associated points to generic points of the target. -/
theorem pullbackDefined_of_associatedPoints_mapsTo_genericPoints
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y)
    (hassoc : Set.MapsTo f.base X.associatedPoints (genericPoints Y)) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom := sorry

/-- A morphism from a locally Noetherian scheme without embedded points preserves regular
meromorphic denominators if it maps the source's generic points to generic points of the target. -/
theorem pullbackDefined_of_genericPoints_mapsTo_of_noEmbeddedPoints
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y)
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (hgeneric : Set.MapsTo f.base (genericPoints X) (genericPoints Y)) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom := sorry

/-- A flat scheme morphism preserves regular meromorphic denominators. -/
theorem pullbackDefined_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined f.toLRSHom := sorry

end AlgebraicGeometry.Scheme.Hom.MeromorphicFunction
