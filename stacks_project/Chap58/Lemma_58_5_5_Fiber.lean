/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap58.Lemma_58_5_2
public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Fiber

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X : Scheme.{u}}

/-- Forget the finiteness component of a finite étale object, retaining its étale structure. -/
abbrev finiteEtaleToEtale (Y : Scheme.FiniteEtale X) : X.Etale :=
  (Scheme.FiniteEtale.toEtale X).obj Y

/-- The morphism of étale objects induced by a morphism in the finite étale category. -/
abbrev finiteEtaleToEtaleMap {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) :
    finiteEtaleToEtale Y ⟶ finiteEtaleToEtale Z :=
  (Scheme.FiniteEtale.toEtale X).map f

/-- The point of the small étale site determined by a geometric point. -/
noncomputable abbrev geometricPointEtalePoint (xbar : Scheme.GeometricPoint X) :
    (smallEtaleTopology X).Point :=
  @Scheme.pointSmallEtale X xbar.K xbar.field
    (@IsSepClosed.of_isAlgClosed xbar.K xbar.field xbar.isAlgClosed) xbar.hom

/-- The carrier of the geometric fiber of a finite étale object at a chosen geometric point. -/
abbrev finiteEtaleFiberObj (xbar : Scheme.GeometricPoint X)
    (Y : Scheme.FiniteEtale X) : Type u :=
  (@Scheme.FiniteEtale.fiber X xbar.K xbar.field xbar.isAlgClosed xbar.hom).obj Y

/-- The geometric fiber of a finite étale object is finite. -/
abbrev finiteEtaleFiberObj_finite (xbar : Scheme.GeometricPoint X)
    (Y : Scheme.FiniteEtale X) : Finite (finiteEtaleFiberObj xbar Y) :=
  @Scheme.FiniteEtale.fiber_obj_finite X xbar.K xbar.field xbar.isAlgClosed xbar.hom Y

/-- The finite-set-valued geometric-fiber functor at a chosen geometric point. -/
noncomputable abbrev finiteEtaleFiber (xbar : Scheme.GeometricPoint X)
    (hfinite : ∀ Y : Scheme.FiniteEtale X, Finite (finiteEtaleFiberObj xbar Y)) :
    Scheme.FiniteEtale X ⥤ FintypeCat.{u} :=
  @Scheme.FiniteEtale.finiteFiber X xbar.K xbar.field xbar.isAlgClosed xbar.hom

/-- The object of `finiteEtaleFiber xbar` at `Y` has the canonical étale-point fiber carrier. -/
abbrev finiteEtaleFiber_obj_apply (xbar : Scheme.GeometricPoint X)
    (hfinite : ∀ Y : Scheme.FiniteEtale X, Finite (finiteEtaleFiberObj xbar Y))
    (Y : Scheme.FiniteEtale X) :
    ((finiteEtaleFiber xbar hfinite).obj Y).obj = finiteEtaleFiberObj xbar Y :=
  @Scheme.FiniteEtale.finiteFiber_obj X xbar.K xbar.field xbar.isAlgClosed xbar.hom Y

/-- The map induced by a finite étale morphism on the canonical geometric-fiber carriers. -/
abbrev finiteEtaleFiber_map_apply (xbar : Scheme.GeometricPoint X)
    (hfinite : ∀ Y : Scheme.FiniteEtale X, Finite (finiteEtaleFiberObj xbar Y))
    {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) (y : finiteEtaleFiberObj xbar Y) :
    ((finiteEtaleFiber xbar hfinite).map f) y =
      (geometricPointEtalePoint xbar).fiber.map (finiteEtaleToEtaleMap f) y :=
  @Scheme.FiniteEtale.finiteFiber_map_apply X xbar.K xbar.field xbar.isAlgClosed
    xbar.hom Y Z f y

/-- The underlying set-valued view of the finite geometric-fiber functor. -/
noncomputable abbrev finiteEtaleFiber_underlying (xbar : Scheme.GeometricPoint X)
    (hfinite : ∀ Y : Scheme.FiniteEtale X, Finite (finiteEtaleFiberObj xbar Y)) :
    Scheme.FiniteEtale X ⥤ Type u :=
  @Scheme.FiniteEtale.fiber X xbar.K xbar.field xbar.isAlgClosed xbar.hom

/-- The underlying carrier of the set-valued geometric-fiber functor is the canonical
étale-point fiber. -/
abbrev finiteEtaleFiber_underlying_obj (xbar : Scheme.GeometricPoint X)
    (hfinite : ∀ Y : Scheme.FiniteEtale X, Finite (finiteEtaleFiberObj xbar Y))
    (Y : Scheme.FiniteEtale X) :
    (finiteEtaleFiber_underlying xbar hfinite).obj Y = finiteEtaleFiberObj xbar Y :=
  @Scheme.FiniteEtale.finiteFiber_obj X xbar.K xbar.field xbar.isAlgClosed xbar.hom Y

end AlgebraicGeometry.Scheme.GeometricPoint
