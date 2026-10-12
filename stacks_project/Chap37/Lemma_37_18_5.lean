/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FlatPointClosure.GenericFlatness
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.18.5 (1): if a finite-type quasicoherent module is flat over the base at
every generic point of every fibre of the canonical map between the reduced closures of
`y` and `f y`, then generic component points of every fibre of the closure of `y` remain
in the relative assassin. -/
@[stacks 0GSJ] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.mem_pointClosureFiber_of_flatAtGenericPoints :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
      [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (y : X) (hy : y ∈ relativeAssassin f ℱ)
      (hflat : ∀ (t : PointClosure.scheme (f y))
        (z : (PointClosure.map f y).fiber t),
        closure ({z} : Set ((PointClosure.map f y).fiber t)) ∈
          irreducibleComponents ((PointClosure.map f y).fiber t) →
        flatOverAt ℱ f (((PointClosure.map f y).fiberι t ≫ PointClosure.ι y) z))
      (s : S) (x : (PointClosure.ι y ≫ f).fiber s)
      (hgeneric : closure ({x} : Set ((PointClosure.ι y ≫ f).fiber s)) ∈
        irreducibleComponents ((PointClosure.ι y ≫ f).fiber s)),
      ((PointClosure.ι y ≫ f).fiberι s ≫ PointClosure.ι y) x ∈ relativeAssassin f ℱ)

/- Lemma 37.18.5 (2): under the same generic-fibre flatness hypothesis, the canonical
dominant map between the reduced closures of `y` and `f y` has some nonnegative relative
dimension. -/
@[stacks 0GSJ] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.exists_pointClosureMap_relativeDimension_of_flatAtGenericPoints :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
      [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (y : X) (hy : y ∈ relativeAssassin f ℱ)
      (hflat : ∀ (t : PointClosure.scheme (f y))
        (z : (PointClosure.map f y).fiber t),
        closure ({z} : Set ((PointClosure.map f y).fiber t)) ∈
          irreducibleComponents ((PointClosure.map f y).fiber t) →
        flatOverAt ℱ f (((PointClosure.map f y).fiberι t ≫ PointClosure.ι y) z)),
      ∃ d : ℕ, Scheme.Hom.RelativeDimension (PointClosure.map f y) d)

end AlgebraicGeometry.Scheme.Modules
