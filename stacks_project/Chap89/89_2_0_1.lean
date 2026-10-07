module

public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap89.«89_2_0_1_ProperIsoOverOpen»
public import stacks_project.Chap89.«89_2_0_1_Punctured»

/-!
# Proper morphisms of algebraic spaces that are isomorphisms over the punctured spectrum
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- 89.2.0.1 For a Noetherian local ring `(A, 𝔪, κ)`, with `S = Spec(A)` and
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

end AlgebraicGeometry.AlgebraicSpace
