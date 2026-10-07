module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import stacks_project.Chap72.Definition_72_8_1_Modification
public import stacks_project.Chap89.«89_2_0_1»

/-!
# Modifications of the spectrum of a 2-dimensional Noetherian local domain
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The spectrum of a domain, viewed as an algebraic space over itself, is integral. -/
instance instIsIntegral_specSpace (A : Type u) [CommRing A] [IsDomain A] :
    IsIntegral (specSpace A) :=
  sorry

/-- Lemma 89.2.1 Let `(A, 𝔪, κ)` be a 2-dimensional Noetherian local domain
such that `U = Spec(A) \ {𝔪}` is a normal scheme. Then any modification
`f : X ⟶ specSpace A` is a morphism as in 89.2.0.1: `f` is proper and
`f⁻¹(U) ⟶ U` is an isomorphism. -/
@[stacks 0AE3]
theorem isProperIsoOverOpen_puncturedι_of_isModification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : ringKrullDim A = 2) (hU : (PuncturedSpectrum.scheme A).isNormal)
    {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X]
    (f : X ⟶ specSpace A) [IsModification f] :
    IsProperIsoOverOpen f (puncturedι A) :=
  sorry

/-- A modification of `specSpace A` is an isomorphism over the punctured
spectrum when `A` is a 2-dimensional Noetherian local domain with normal
punctured spectrum. -/
theorem isIsoOverOpen_puncturedι_of_isModification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : ringKrullDim A = 2) (hU : (PuncturedSpectrum.scheme A).isNormal)
    {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X]
    (f : X ⟶ specSpace A) [IsModification f] :
    IsIsoOverOpen f (puncturedι A) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
