module

import StacksCheckRecall
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap89.«89_2_0_1_ProperIsoOverOpen»
public import stacks_project.Chap89.«89_2_0_1_Punctured»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProperIsoOverPuncturedSpectrum

/-!
# Proper morphisms of algebraic spaces that are isomorphisms over the punctured spectrum
-/

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- 89.2.0.1 For a Noetherian local ring `(A, 𝔪, κ)`, with `S = Spec(A)` and
`U = S \ {𝔪}`, the category of morphisms `f : X ⟶ S` of algebraic spaces such
that `f` is proper and `f⁻¹(U) ⟶ U` is an isomorphism. Morphisms `X / S ⟶ X' / S`
are morphisms of algebraic spaces over `S`. -/
@[stacks 0AE2] #check (AlgebraicGeometry.AlgebraicSpace.ProperIsoOverPuncturedSpectrum :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.properIsoOverPuncturedSpectrum_iff :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : Over (specSpace A)),
    properIsoOverOpenProperty (puncturedι A) X ↔
      Proper X.hom ∧ IsIsoOverOpen X.hom (puncturedι A))
