module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.NonCompact
import StacksCheckRecall

@[expose] public section

universe u v

open ProjectiveSpectrum AlgebraicGeometry CategoryTheory

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Part (1): `D₊(f)` is the open set `basicOpen 𝒜 f` in
`ProjectiveSpectrum 𝒜`. -/
#check (ProjectiveSpectrum.isOpen_basicOpen 𝒜 :
  ∀ {f : A}, IsOpen (basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)))

/- Part (2): `D₊(f * f') = D₊(f) ∩ D₊(f')` is `basicOpen_mul`. -/
#check (ProjectiveSpectrum.basicOpen_mul 𝒜 :
  ∀ f f' : A, basicOpen 𝒜 (f * f') = basicOpen 𝒜 f ⊓ basicOpen 𝒜 f')

/- Part (3): identifying `D(g) ∩ Proj` with `basicOpen 𝒜 g`, this equals the
union of `D(g₀) ∩ Proj` and the positive-degree standard opens `D₊(gᵢ)` for the homogeneous
components `gᵢ = GradedRing.proj 𝒜 i g`. -/
#check (ProjectiveSpectrum.basicOpen_eq_projZero_sup_iSup_pos 𝒜 : ∀ g : A,
    basicOpen 𝒜 g =
      basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g))

#check (ProjectiveSpectrum.mem_basicOpen_eq_projZero_sup_iSup_pos 𝒜 :
  ∀ (g : A) (x : ProjectiveSpectrum 𝒜),
    x ∈ basicOpen 𝒜 g ↔
      x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ∨
        ∃ i : {n : ℕ // 1 ≤ n}, x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g))

/- Part (4): if `g₀` is homogeneous of degree 0, then `D(g₀) ∩ Proj` is the union
of the positive-degree standard opens `D₊(g₀ * f)` as `f` runs over homogeneous elements of
positive degree. -/
#check (ProjectiveSpectrum.basicOpen_degreeZero_eq_iSup_mul 𝒜 : ∀ g₀ : 𝒜 0,
    basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1,
        basicOpen 𝒜 ((g₀ : A) * (f : A)))

#check (ProjectiveSpectrum.mem_basicOpen_degreeZero_iff 𝒜 :
  ∀ (g₀ : 𝒜 0) (x : ProjectiveSpectrum 𝒜),
    x ∈ basicOpen 𝒜 (g₀ : A) ↔
      ∃ d : ℕ, ∃ f : 𝒜 d, 0 < d ∧ x ∈ basicOpen 𝒜 ((g₀ : A) * (f : A)))

/- Exercise 111.27.4 (5): the positive-degree homogeneous opens `{D₊(f)}` form a basis of
`ProjectiveSpectrum 𝒜`. -/
@[stacks 02E9] #check (ProjectiveSpectrum.isTopologicalBasis_positiveDegree_basic_opens 𝒜 :
  TopologicalSpace.IsTopologicalBasis
    {U : Set (ProjectiveSpectrum 𝒜) |
      ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧
        U = (basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜))})

end

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Part (6): for homogeneous `f ∈ 𝒜 m` of positive degree, there is a canonical
bijection `D₊(f) → Spec(HomogeneousLocalization.Away 𝒜 f)`. -/
#check (AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_bijective 𝒜 :
  ∀ {f : A} {m : ℕ}, f ∈ 𝒜 m → 0 < m →
    Function.Bijective (AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec 𝒜 f))

/- Part (7): the bijection of (6) is a homeomorphism. -/
#check (AlgebraicGeometry.projIsoSpecTopComponent :
  ∀ {f : A} {m : ℕ}, f ∈ 𝒜 m → 0 < m →
    Iso (C := TopCat) (TopCat.of (basicOpen 𝒜 f))
      (TopCat.of (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f))))

end

/- Part (8): the projective spectrum of the standard-graded polynomial ring
`MvPolynomial ℕ ℤ` is not quasi-compact. -/
#check (not_isCompactSpace_projectiveSpectrum_mvPolynomial_nat_int :
  ¬ CompactSpace (ProjectiveSpectrum (MvPolynomial.standardGrading ℕ ℤ)))

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Part (9): every closed subset `T` of `ProjectiveSpectrum 𝒜` equals `V₊(I)` for
the homogeneous ideal `I = vanishingIdeal T`. -/
#check (ProjectiveSpectrum.exists_homogeneousIdeal_zeroLocus_of_isClosed 𝒜 :
  ∀ T : Set (ProjectiveSpectrum 𝒜), IsClosed T →
    ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A))

end
