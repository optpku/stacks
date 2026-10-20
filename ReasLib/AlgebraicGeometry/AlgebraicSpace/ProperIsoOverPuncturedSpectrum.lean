/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PuncturedSpectrum

/-!
# Proper morphisms of algebraic spaces that are isomorphisms over the punctured spectrum
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a Noetherian local ring `(A, 𝔪, κ)`, with `S = Spec(A)` and
`U = S \ {𝔪}`, the category of morphisms `f : X ⟶ S` of algebraic spaces such
that `f` is proper and `f⁻¹(U) ⟶ U` is an isomorphism. Morphisms `X / S ⟶ X' / S`
are morphisms of algebraic spaces over `S`. -/
@[stacks 0AE2]
abbrev ProperIsoOverPuncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :=
  ProperIsoOverOpen (puncturedι A)

/-- Membership of a morphism over `specSpace A` in the object property of
`ProperIsoOverPuncturedSpectrum A` is properness together with being an
isomorphism over the punctured spectrum. -/
theorem properIsoOverPuncturedSpectrum_iff (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (X : Over (specSpace A)) :
    properIsoOverOpenProperty (puncturedι A) X ↔
      Proper X.hom ∧ IsIsoOverOpen X.hom (puncturedι A) :=
  sorry

/-- A morphism between proper algebraic spaces over the spectrum of a Noetherian
local ring, both isomorphisms over the punctured spectrum, is a closed immersion
if its induced morphism on special fibres is a closed immersion. -/
@[stacks 0AGM]
theorem IsClosedImmersion.of_specialFiber
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X Y : AlgebraicSpace (Spec (.of A))} (g : X ⟶ Y) (q : Y ⟶ specSpace A)
    (hX : IsProperIsoOverOpen (g ≫ q) (puncturedι A))
    (hY : IsProperIsoOverOpen q (puncturedι A))
    [IsClosedImmersion
      (overBaseChange g q (residueFieldHom (Spec (.of A)) (IsLocalRing.closedPoint A)))] :
    IsClosedImmersion g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
