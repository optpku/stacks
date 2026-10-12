/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Affine

/-!
# Projection formula for affine morphisms

This module records the affine pullback-pushforward formula for derived modules with
quasicoherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For an affine morphism `f : X ⟶ S`, derived pushforward after derived pullback of
`E` is isomorphic to `E` derived-tensored with the underived direct image `f_*𝒪_X`. -/
theorem affinePushforwardPullback_isomorphic {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] (E : Scheme.ModuleDerived.Quasicoherent S) :
    IsIsomorphic
      ((pushforwardCohomologyIn f).obj ((pullback f).obj E))
      (tensorObj E (pushforwardStructureSheaf f)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
