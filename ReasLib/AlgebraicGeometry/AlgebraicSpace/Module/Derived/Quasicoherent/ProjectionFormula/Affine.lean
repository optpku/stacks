module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Qcqs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Tensor
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Projection formula for affine morphisms of algebraic spaces

Derived pushforward after derived pullback is isomorphic to derived tensor with
the underived direct image of the structure sheaf for an affine morphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- For an affine morphism `f : X ⟶ Y` of algebraic spaces over `S`, derived
pushforward after derived pullback of `E` is isomorphic to `E` derived-tensored
with the underived direct image `f_* 𝒪_X`. -/
theorem affinePushforwardPullback_isomorphic (f : X ⟶ Y) [Affine f]
    (E : DerivedQCoh Y) :
    IsIsomorphic ((pushforwardCohomologyIn f).obj ((pullback f).obj E))
      (tensorObj E (pushforwardStructureSheaf f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
