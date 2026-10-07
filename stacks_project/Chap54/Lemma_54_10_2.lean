module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ArcRegularity

@[expose] public section

open AlgebraicGeometry

universe u

-- Local instance justification (search instability): `Localization.AtPrime (RingHom.ker f)` needs the canonical primality theorem, which mathlib does not register globally.
attribute [local instance] RingHom.ker_isPrime

/- Lemma 54.10.2: for a surjection from a two-dimensional Noetherian local domain onto a
complete discrete valuation ring, a point in the associated sequence of blowups eventually lies
in the regular locus, provided the localization at the kernel is a regular local ring. -/
@[stacks 0BG3] #check
  (AlgebraicGeometry.Scheme.exists_mem_regularLocus_of_regular_ker :
    ∀ (A R : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
      [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R],
      (f : A →+* R) → Function.Surjective f → ringKrullDim A = 2 →
      (S : AlgebraicGeometry.Scheme.Hom.PointBlowupSequence
        (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint R)) →
      IsRegularLocalRing (Localization.AtPrime (RingHom.ker f)) →
      ∃ i : ℕ,
        S.point i ∈ AlgebraicGeometry.Scheme.regularLocus (S.stage i))
