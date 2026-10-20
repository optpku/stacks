/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Scheme-theoretic images of reduced algebraic spaces

The scheme-theoretic image of a morphism from a reduced algebraic space is the
reduced induced closed structure on the closure of its point-image. Formation
of this image commutes with étale base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The closure of the point-image of a morphism in the canonical topology. -/
def rangeClosure {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points Y) :=
  closure (Set.range (Points.map f))

namespace IsSchemeTheoreticImage

/-- A scheme-theoretic image of a morphism from a reduced algebraic space is reduced. -/
theorem isReduced {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (toImage : X ⟶ Z) (ι : Z ⟶ Y) [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] : IsReduced Z :=
  sorry

/-- The points of a scheme-theoretic image of a morphism from a reduced algebraic
space form the closure of its point-image in the canonical topology. -/
theorem range_eq_rangeClosure {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] :
    Set.range (Points.map ι) = rangeClosure f :=
  sorry

/-- A factorization of a morphism from a reduced algebraic space is a
scheme-theoretic image exactly when it is a reduced closed subspace whose
points form the closure of the point-image of the morphism. -/
theorem iff_isReduced_range_eq_rangeClosure {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced X] (f : X ⟶ Y) (toImage : X ⟶ Z)
    (ι : Z ⟶ Y) :
    IsSchemeTheoreticImage f toImage ι ↔
      toImage ≫ ι = f ∧ IsClosedImmersion ι ∧ IsReduced Z ∧
        Set.range (Points.map ι) = rangeClosure f :=
  sorry

/-- A reduced closed subspace through which a morphism from a reduced algebraic
space factors is its scheme-theoretic image if its points form the closure of
the point-image of the morphism. -/
theorem of_isReduced_range_eq_rangeClosure {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced X] (f : X ⟶ Y) (toImage : X ⟶ Z)
    (ι : Z ⟶ Y) [IsClosedImmersion ι] [IsReduced Z] (hfac : toImage ≫ ι = f)
    (hsupport : Set.range (Points.map ι) = rangeClosure f) :
    IsSchemeTheoreticImage f toImage ι :=
  sorry

/-- Scheme-theoretic images of morphisms from reduced algebraic spaces commute
with étale base change, as a statement about chosen pullbacks. -/
instance of_pullback_etale {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [Etale φ]
    [HasPullback f φ] [HasPullback ι φ] :
    IsSchemeTheoreticImage (pullback.snd f φ) (pullbackToImage f toImage ι φ)
      (pullback.snd ι φ) :=
  sorry

/-- For an étale morphism `φ : V ⟶ Y`, the scheme-theoretic image of
`X ×_Y V ⟶ V` for reduced `X` is the closed inverse image `Z ×_Y V` of the
scheme-theoretic image of `X ⟶ Y`. -/
instance of_inverseImage_etale {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [Etale φ] [HasPullback f φ] :
    IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToInverseImage f toImage ι φ) (inverseImageι φ ι) :=
  sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicSpace
