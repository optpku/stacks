/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap68.Lemma_68_18_6_Fibre

/-!
# Finite-freeness in an étale neighbourhood of an algebraic space

A finitely presented module on an algebraic space is finite free at a point when it
becomes finite free on a Zariski open of some étale scheme neighbourhood. The geometric
fibre of a morphism at a geometric point supplies the corresponding stalk and
neighbourhood tests over `X_ybar`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open IsLocalRing TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The extended maximal ideal `m_ybar 𝒪_{X, xbar}` in the étale local ring of `X` at a
geometric point `xbar`, for `ybar = xbar.map f`. -/
noncomputable def geometricFiberIdeal (f : X ⟶ Y) (xbar : GeometricPoint X) :
    Ideal (etaleLocalRing X xbar) :=
  (maximalIdeal (etaleLocalRing Y (xbar.map f))).map (etaleLocalRingMap f xbar)

/-- `geometricFiberIdeal f xbar` is the extension of the maximal ideal of
`𝒪_{Y, ybar}` along `etaleLocalRingMap f xbar`. -/
theorem geometricFiberIdeal_eq (f : X ⟶ Y) (xbar : GeometricPoint X) :
    geometricFiberIdeal f xbar =
      (maximalIdeal (etaleLocalRing Y (xbar.map f))).map (etaleLocalRingMap f xbar) :=
  sorry

/-- The geometric-fibre local ring `𝒪_{X_ybar, xbar} = 𝒪_{X, xbar} / m_ybar 𝒪_{X, xbar}`. -/
noncomputable abbrev geometricFiberRing (f : X ⟶ Y) (xbar : GeometricPoint X) :=
  etaleLocalRing X xbar ⧸ geometricFiberIdeal f xbar

/-- `geometricFiberRing f xbar` is the quotient of `etaleLocalRing X xbar` by
`geometricFiberIdeal f xbar`. -/
theorem geometricFiberRing_eq (f : X ⟶ Y) (xbar : GeometricPoint X) :
    geometricFiberRing f xbar =
      (etaleLocalRing X xbar ⧸ geometricFiberIdeal f xbar) :=
  sorry

/-- The geometric-fibre stalk `(F_ybar)_xbar = F_xbar / m_ybar F_xbar`. -/
noncomputable abbrev geometricFiberStalk (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) :=
  stalkModuleCat xbar F ⧸
    (geometricFiberIdeal f xbar •
      (⊤ : Submodule (etaleLocalRing X xbar) (stalkModuleCat xbar F)))

/-- `geometricFiberStalk F f xbar` is the quotient of the étale stalk by the extended
maximal ideal of `𝒪_{Y, ybar}`. -/
theorem geometricFiberStalk_eq (F : X.Modules) (f : X ⟶ Y) (xbar : GeometricPoint X) :
    geometricFiberStalk F f xbar =
      (stalkModuleCat xbar F ⧸
        (geometricFiberIdeal f xbar •
          (⊤ : Submodule (etaleLocalRing X xbar) (stalkModuleCat xbar F)))) :=
  sorry

/-- The geometric-fibre stalk is a flat module over `𝒪_{X_ybar, xbar}`. -/
def geometricFiberStalk_isFlat (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) : Prop :=
  Module.Flat (geometricFiberRing f xbar) (geometricFiberStalk F f xbar)

/-- `geometricFiberStalk_isFlat` is `Module.Flat` of the geometric-fibre stalk over the
geometric-fibre local ring. -/
theorem geometricFiberStalk_isFlat_iff (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    geometricFiberStalk_isFlat F f xbar ↔
      Module.Flat (geometricFiberRing f xbar) (geometricFiberStalk F f xbar) :=
  sorry

/-- The geometric-fibre stalk is a free module over `𝒪_{X_ybar, xbar}`. -/
def geometricFiberStalk_isFree (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) : Prop :=
  Module.Free (geometricFiberRing f xbar) (geometricFiberStalk F f xbar)

/-- `geometricFiberStalk_isFree` is `Module.Free` of the geometric-fibre stalk over the
geometric-fibre local ring. -/
theorem geometricFiberStalk_isFree_iff (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    geometricFiberStalk_isFree F f xbar ↔
      Module.Free (geometricFiberRing f xbar) (geometricFiberStalk F f xbar) :=
  sorry

/-- The identity-on-`Spec(k)` square used to lift `xbar` into the field-valued fibre
`X ×_Y Spec(k)`. -/
theorem geometricFiberPoint_w (f : X ⟶ Y) (xbar : GeometricPoint X) :
    xbar.hom ≫ f = 𝟙 (ofOver xbar.overObj) ≫ (xbar.map f).hom :=
  sorry

/-- The field-valued point of `X_ybar = X ×_Y Spec(k)` induced by a geometric point of `X`. -/
noncomputable def geometricFiberPoint (f : X ⟶ Y) (xbar : GeometricPoint X) :
    FieldValuedPoint (fieldFiber f (xbar.map f).toFieldValuedPoint) :=
  FieldValuedPoint.of xbar.K xbar.structureHom
    (Limits.pullback.lift xbar.hom (𝟙 (ofOver xbar.overObj))
      (geometricFiberPoint_w f xbar))

/-- The morphism of `geometricFiberPoint f xbar` is the universal lift of `xbar.hom` against
`f`. -/
theorem geometricFiberPoint_hom (f : X ⟶ Y) (xbar : GeometricPoint X) :
    (geometricFiberPoint f xbar).hom =
      Limits.pullback.lift xbar.hom (𝟙 (ofOver xbar.overObj))
        (geometricFiberPoint_w f xbar) :=
  sorry

/-- `F` is finite free in an étale neighbourhood of a point `x` of `|X|`. -/
def finiteFreeEtaleAt (F : X.Modules) (x : Points X) : Prop :=
  ∃ (U : smallEtaleSite X) (u : U.left.left) (W : Opens U.left.left),
    Points.map U.hom (ofOver.pointsEquiv U.left u) = x ∧
      u ∈ W ∧ SheafOfModules.IsFiniteFree (((restrictToScheme U).obj F).over W)

/-- `finiteFreeEtaleAt F x` unpacks as an étale scheme neighbourhood of `x` on which a
Zariski restriction of `F` is finite free. -/
theorem finiteFreeEtaleAt_iff (F : X.Modules) (x : Points X) :
    finiteFreeEtaleAt F x ↔
      ∃ (U : smallEtaleSite X) (u : U.left.left) (W : Opens U.left.left),
        Points.map U.hom (ofOver.pointsEquiv U.left u) = x ∧
          u ∈ W ∧ SheafOfModules.IsFiniteFree (((restrictToScheme U).obj F).over W) :=
  sorry

/-- The pullback of `F` to the geometric fibre `X_ybar` is finite free in an étale
neighbourhood of the induced point over `xbar`. -/
def finiteFreeEtaleAt_fiber (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) : Prop :=
  finiteFreeEtaleAt ((pullback (fieldFiberι f (xbar.map f).toFieldValuedPoint)).obj F)
    (Points.mk (geometricFiberPoint f xbar))

/-- `finiteFreeEtaleAt_fiber` is `finiteFreeEtaleAt` of the pullback of `F` along
`fieldFiberι` at `geometricFiberPoint f xbar`. -/
theorem finiteFreeEtaleAt_fiber_iff (F : X.Modules) (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    finiteFreeEtaleAt_fiber F f xbar ↔
      finiteFreeEtaleAt ((pullback (fieldFiberι f (xbar.map f).toFieldValuedPoint)).obj F)
        (Points.mk (geometricFiberPoint f xbar)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
