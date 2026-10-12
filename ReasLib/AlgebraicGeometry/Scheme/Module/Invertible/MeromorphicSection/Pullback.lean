/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.IrreducibleComponents

/-!
# Pullback of meromorphic sections of invertible modules

Dominant morphisms of integral schemes preserve nonvanishing when meromorphic sections of
invertible modules are pulled back.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.MeromorphicFunction

/-- Pullback of a nonzero meromorphic section along a dominant morphism of integral schemes is
nonzero. -/
theorem pullbackSections_ne_zero_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (ℒ : Y.Modules) [Modules.Invertible ℒ]
    (s : Y.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    LocallyRingedSpace.Hom.pullbackMeromorphicSections f.toLRSHom
      (pullbackDefined_of_isIntegral_of_isDominant f) ℒ s ≠ 0 := sorry

/-- Pullback of meromorphic functions to the reduced closure of an irreducible component of
the source of a flat morphism to an integral scheme is defined. -/
theorem pullbackDefined_toFlatComponent
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (C : irreducibleComponents X) :
    LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined
      (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f).toLRSHom := sorry

end AlgebraicGeometry.Scheme.Hom.MeromorphicFunction

namespace AlgebraicGeometry.Scheme.Modules.MeromorphicSection

/-- Pull a meromorphic section back to the reduced closure of an irreducible component of the
source of a flat morphism to an integral scheme. -/
noncomputable def pullbackToFlatComponent
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (ℒ : Y.Modules) [Invertible ℒ]
    (s : Y.toLocallyRingedSpace.meromorphicSections ℒ)
    (C : irreducibleComponents X) :
    (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1).toLocallyRingedSpace.meromorphicSections
      ((Scheme.Modules.pullback
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f)).obj ℒ) :=
  LocallyRingedSpace.Hom.pullbackMeromorphicSections
    (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f).toLRSHom
    (Scheme.Hom.MeromorphicFunction.pullbackDefined_toFlatComponent f C) ℒ s

/-- Pullback to a flat-source component is the direct meromorphic-section pullback along the
component-to-target composite. -/
theorem pullbackToFlatComponent_eq
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (ℒ : Y.Modules) [Invertible ℒ]
    (s : Y.toLocallyRingedSpace.meromorphicSections ℒ)
    (C : irreducibleComponents X) :
    pullbackToFlatComponent f ℒ s C =
      LocallyRingedSpace.Hom.pullbackMeromorphicSections
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f).toLRSHom
        (Scheme.Hom.MeromorphicFunction.pullbackDefined_toFlatComponent f C) ℒ s := sorry

/-- A nonzero meromorphic section remains nonzero after pullback to every reduced irreducible
component of the source of a flat morphism to an integral scheme. -/
theorem pullbackToFlatComponent_ne_zero
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    (ℒ : Y.Modules) [Invertible ℒ]
    (s : Y.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (C : irreducibleComponents X) :
    pullbackToFlatComponent f ℒ s C ≠ 0 := sorry

end AlgebraicGeometry.Scheme.Modules.MeromorphicSection
