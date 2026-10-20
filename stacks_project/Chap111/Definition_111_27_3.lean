/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Subring
import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Locus
import StacksCheckRecall

@[expose] public section

universe u v

open HomogeneousLocalization ProjectiveSpectrum

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (f : A) (I : HomogeneousIdeal 𝒜)

section

variable (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)

/- Definition 111.27.3 (1): for an `ℕ`-graded ring `𝒜`, `f ∈ 𝒜 d`, and `0 < d`, the source's
degree-zero homogeneous localization is the range subring of the ordinary localization. -/
@[stacks 0283]
 #check (HomogeneousLocalization.Away.subring 𝒜 f : Subring (Localization (Submonoid.powers f)))

/- The embedding of `Away 𝒜 f` into `Localization (Submonoid.powers f)` is the injective map
`val`. -/
#check (HomogeneousLocalization.val :
    HomogeneousLocalization.Away 𝒜 f → Localization (Submonoid.powers f))

#check HomogeneousLocalization.val_injective (Submonoid.powers f)

/- Source fractions `r / f ^ n` with `r` homogeneous of degree `n • d` are constructed by
`Away.mk`. -/
#check HomogeneousLocalization.Away.mk 𝒜 hf

#check HomogeneousLocalization.Away.mk_surjective 𝒜 hf

#check fun n x hx ↦ HomogeneousLocalization.Away.val_mk 𝒜 n hf x hx

#check HomogeneousLocalization.Away.mem_subring_iff (𝒜 := 𝒜) hf

/- Definition 111.27.3 (2): for `f ∈ 𝒜 d` with `0 < d`, the source's `D₊(f)` is
the preimage of the ordinary distinguished open under the underlying-prime map. -/
@[stacks 0283]
 #check (ProjectiveSpectrum.basicOpen_eq_preimage 𝒜 f :
    (ProjectiveSpectrum.basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)) =
      ProjectiveSpectrum.toPrimeSpectrum 𝒜 ⁻¹'
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)))

/- Membership in `basicOpen 𝒜 f` is the source set-builder of points not containing `f`. -/
#check ProjectiveSpectrum.mem_basicOpen 𝒜 f

#check ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl 𝒜 f

end

/- Definition 111.27.3 (3): for a homogeneous ideal `I`, the source's `V₊(I)` is
the preimage of the ordinary vanishing locus under the underlying-prime map. -/
@[stacks 0283]
 #check (ProjectiveSpectrum.zeroLocus_eq_preimage 𝒜 (I : Set A) :
    ProjectiveSpectrum.zeroLocus 𝒜 (I : Set A) =
      ProjectiveSpectrum.toPrimeSpectrum 𝒜 ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))

/- Membership in `zeroLocus` is containment of `I` in the homogeneous prime. -/
#check fun x ↦ ProjectiveSpectrum.mem_zeroLocus 𝒜 x (I : Set A)

end
