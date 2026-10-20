module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GeometricFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Data.List.TFAE

/-!
# Finite freeness near a point of an algebraic space

Finite freeness in an étale neighbourhood is equivalent to flatness or freeness
of the geometric-fibre stalk for a finitely presented module relatively flat at
the point over a locally finitely presented morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A module is finite free in an étale neighbourhood of a point if its restriction
to an étale scheme chart is finite free on an open neighbourhood of a point over it. -/
def finiteFreeEtaleAt (F : X.Modules) (x : Points X) : Prop :=
  ∃ (U : smallEtaleSite X) (u : U.left.left) (W : Opens U.left.left),
    Points.map U.hom (ofOver.pointsEquiv U.left u) = x ∧
      u ∈ W ∧ SheafOfModules.IsFiniteFree (((restrictToEtaleScheme U).obj F).over W)

/-- Finite freeness near a point is the existence of an étale chart and an open
neighbourhood on which the restricted module is finite free. -/
theorem finiteFreeEtaleAt_iff (F : X.Modules) (x : Points X) :
    finiteFreeEtaleAt F x ↔
      ∃ (U : smallEtaleSite X) (u : U.left.left) (W : Opens U.left.left),
        Points.map U.hom (ofOver.pointsEquiv U.left u) = x ∧
          u ∈ W ∧ SheafOfModules.IsFiniteFree (((restrictToEtaleScheme U).obj F).over W) :=
  Iff.rfl

/-- The pullback module on the geometric fibre is finite free in an étale
neighbourhood of the induced geometric point. -/
def finiteFreeEtaleAt_fiber (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) : Prop :=
  finiteFreeEtaleAt ((pullback (fieldFiberι f (xbar.map f).toFieldValuedPoint)).obj F)
    (geometricFiberPoint f xbar).image

/-- Finite freeness near the geometric-fibre point is finite freeness of the
pulled-back module near the image of the induced geometric point. -/
theorem finiteFreeEtaleAt_fiber_iff (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    finiteFreeEtaleAt_fiber F f xbar ↔
      finiteFreeEtaleAt ((pullback (fieldFiberι f (xbar.map f).toFieldValuedPoint)).obj F)
        (geometricFiberPoint f xbar).image :=
  Iff.rfl

/-- For a finitely presented module flat at a point over a locally finitely
presented morphism, flatness and freeness of the geometric-fibre stalk, finite
freeness near the geometric-fibre point, and finite freeness near the original
point are equivalent. -/
theorem finiteFreeEtaleAt_tfae (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (x : Points X) (xbar : GeometricPoint X)
    (hx : xbar.liesOver x) (h_flat : flatOverAt F f x) :
    List.TFAE
      [Module.Flat (geometricFiberRing f xbar) (geometricFiberStalk F f xbar),
        Module.Free (geometricFiberRing f xbar) (geometricFiberStalk F f xbar),
        finiteFreeEtaleAt_fiber F f xbar, finiteFreeEtaleAt F x] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
