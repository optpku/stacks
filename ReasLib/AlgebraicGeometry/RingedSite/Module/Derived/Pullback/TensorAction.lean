/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition
public import ReasLib.CategoryTheory.Monoidal.Action.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor actions and composition of derived pullbacks

The comparison from iterated derived pullback to pullback along a composite induces a comparison
between the corresponding right tensor actions.  This is the presentation-independent core of
change-of-rings tensor identities such as Stacks Project, Lemma 21.18.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom.modulePullbackDerived.TensorAction

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}
variable [hX : UnivLE.{max uX vX, z}] [hY : UnivLE.{max uY vY, z}]
  [hZ : UnivLE.{max uZ vZ, z}]
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
variable [(f.modulePushforward.{z}).IsRightAdjoint]
  [(g.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{z} g) (ModuleQis.{z} Z)]
  [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{z} (f.comp g)) (ModuleQis.{z} Z)]
variable [MonoidalCategory (@ModuleDerived.{z, uX, vX, w} X hX)]

/-- The iterated derived pullback functor associated to composable ringed-site morphisms. -/
abbrev iterated :
    (@ModuleDerived.{z, uZ, vZ, w} Z hZ) ⥤
      (@ModuleDerived.{z, uX, vX, w} X hX) :=
  modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f

/-- Derived pullback along the composite of two ringed-site morphisms. -/
abbrev composite :
    (@ModuleDerived.{z, uZ, vZ, w} Z hZ) ⥤
      (@ModuleDerived.{z, uX, vX, w} X hX) :=
  modulePullbackDerived.{z} (f.comp g)

/-- The tensor-action comparison induced by the canonical comparison from iterated derived
pullback to pullback along a composite. -/
@[stacks 08I6 "tensor action of a derived-pullback composite"]
def comparison :
    Functor.tensorRightAction
        (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
        (D := @ModuleDerived.{z, uX, vX, w} X hX)
        (iterated (hX := hX) (hY := hY) (hZ := hZ) f g) ⟶
      Functor.tensorRightAction
        (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
        (D := @ModuleDerived.{z, uX, vX, w} X hX)
        (composite (hX := hX) (hZ := hZ) f g) :=
  Functor.tensorRightActionMap
    (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
    (D := @ModuleDerived.{z, uX, vX, w} X hX)
    (modulePullbackDerived.compComparison f g)

variable [IsIso (modulePullbackDerived.compComparison f g)]

/-- The right tensor action of pullback along a composite is canonically isomorphic to the
action of the iterated derived pullback, provided the pullback comparison is invertible. -/
@[stacks 08I6 "tensor action comparison isomorphism"]
def natIso :
    Functor.tensorRightAction
        (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
        (D := @ModuleDerived.{z, uX, vX, w} X hX)
        (composite (hX := hX) (hZ := hZ) f g) ≅
      Functor.tensorRightAction
        (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
        (D := @ModuleDerived.{z, uX, vX, w} X hX)
        (iterated (hX := hX) (hY := hY) (hZ := hZ) f g) :=
  (Functor.tensorRightActionIso
    (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
    (D := @ModuleDerived.{z, uX, vX, w} X hX)
    (asIso (modulePullbackDerived.compComparison f g))).symm

/-- The pointwise tensor-action isomorphism for a composite derived pullback. -/
@[stacks 08I6 "pointwise tensor action comparison"]
abbrev iso
    (M : @ModuleDerived.{z, uX, vX, w} X hX)
    (K : @ModuleDerived.{z, uZ, vZ, w} Z hZ) :
    Functor.tensorRightActionObj
        (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
        (D := @ModuleDerived.{z, uX, vX, w} X hX)
        (composite (hX := hX) (hZ := hZ) f g) M K ≅
      Functor.tensorRightActionObj
        (C := @ModuleDerived.{z, uZ, vZ, w} Z hZ)
        (D := @ModuleDerived.{z, uX, vX, w} X hX)
        (iterated (hX := hX) (hY := hY) (hZ := hZ) f g) M K :=
  (natIso (hX := hX) (hY := hY) (hZ := hZ) f g).app (M, K)

/-- The inverse of `natIso` is the tensor-action comparison induced by the underlying derived
pullback comparison. -/
@[simp]
theorem natIso_inv :
    (natIso (hX := hX) (hY := hY) (hZ := hZ) f g).inv =
      comparison (hX := hX) (hY := hY) (hZ := hZ) f g := sorry

end RingedSite.Hom.modulePullbackDerived.TensorAction

-- The isomorphism data is assembled from the caller-supplied `IsIso` instance; no theorem in
-- this file is installed as inverse data.
