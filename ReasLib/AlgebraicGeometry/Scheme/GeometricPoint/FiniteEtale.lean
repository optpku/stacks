/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Galois
public import ReasLib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.FintypeCat

@[expose] public section

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X Y : Scheme.{u}}

/-- The finite-set-valued geometric-fiber functor at a geometric point. -/
noncomputable abbrev finiteFiber {X : Scheme.{u}} (xbar : GeometricPoint X) :
    Scheme.FiniteEtale X ⥤ FintypeCat.{u} :=
  @Scheme.FiniteEtale.finiteFiber X xbar.K xbar.field xbar.isAlgClosed xbar.hom

/-- The finite fiber comparison induced by the slice pullback adjunction. -/
noncomputable def finiteFiberBaseChangeIso [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    Scheme.finiteEtaleBaseChange f ⋙ finiteFiber xbar ≅ finiteFiber (map xbar f) :=
  NatIso.ofComponents (fun V ↦
    FintypeCat.equivEquivIso <|
      ((Over.mapPullbackAdj f).homEquiv (Over.mk xbar.hom) (Over.mk V.hom)).symm)
    (fun _ ↦ sorry)

/-- The fiber comparison sends a lift to its composite with the pullback projection. -/
theorem finiteFiberBaseChangeIso_hom_apply [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) (xbar : GeometricPoint X) (V : Scheme.FiniteEtale Y)
    (a : (finiteFiber xbar).obj ((Scheme.finiteEtaleBaseChange f).obj V)) :
    ((finiteFiberBaseChangeIso f xbar).hom.app V a).left =
      a.left ≫ CategoryTheory.Limits.pullback.fst V.hom f := sorry

/-- The finite étale action functor associated with a geometric fiber. -/
noncomputable abbrev fiberAction {X : Scheme.{u}} [ConnectedSpace X]
    (xbar : GeometricPoint X) :
    Scheme.FiniteEtale X ⥤ ContAction FintypeCat (Aut (finiteFiber xbar)) :=
  functorToContAction (finiteFiber xbar)

end AlgebraicGeometry.Scheme.GeometricPoint
