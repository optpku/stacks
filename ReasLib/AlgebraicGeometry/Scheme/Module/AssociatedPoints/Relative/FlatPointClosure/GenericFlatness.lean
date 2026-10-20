/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FlatPointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

/-- If a finite-type quasicoherent module is flat over the base at every generic point of
every fibre of the canonical map between the reduced closures of `y` and `f y`, then generic
component points of every fibre of the closure of `y` remain in the relative assassin. -/
theorem mem_pointClosureFiber_of_flatAtGenericPoints {X S : Scheme.{u}}
    (f : X ⟶ S) (ℱ : X.Modules) [LocallyOfFiniteType f]
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : X) (hy : y ∈ relativeAssassin f ℱ)
    (hflat : ∀ (t : PointClosure.scheme (f y))
      (z : (PointClosure.map f y).fiber t),
      closure ({z} : Set ((PointClosure.map f y).fiber t)) ∈
        irreducibleComponents ((PointClosure.map f y).fiber t) →
      flatOverAt ℱ f (((PointClosure.map f y).fiberι t ≫ PointClosure.ι y) z))
    (s : S) (x : (PointClosure.ι y ≫ f).fiber s)
    (hgeneric : closure ({x} : Set ((PointClosure.ι y ≫ f).fiber s)) ∈
      irreducibleComponents ((PointClosure.ι y ≫ f).fiber s)) :
    ((PointClosure.ι y ≫ f).fiberι s ≫ PointClosure.ι y) x ∈
      relativeAssassin f ℱ := sorry

/-- Under uniform generic-fibre flatness, the canonical dominant map between the reduced
closures of a relative-assassin point and its image has some nonnegative relative dimension. -/
theorem exists_pointClosureMap_relativeDimension_of_flatAtGenericPoints
    {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [LocallyOfFiniteType f]
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : X) (hy : y ∈ relativeAssassin f ℱ)
    (hflat : ∀ (t : PointClosure.scheme (f y))
      (z : (PointClosure.map f y).fiber t),
      closure ({z} : Set ((PointClosure.map f y).fiber t)) ∈
        irreducibleComponents ((PointClosure.map f y).fiber t) →
      flatOverAt ℱ f (((PointClosure.map f y).fiberι t ≫ PointClosure.ι y) z)) :
    ∃ d : ℕ, Scheme.Hom.RelativeDimension (PointClosure.map f y) d := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin
