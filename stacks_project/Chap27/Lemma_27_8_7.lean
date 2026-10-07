module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import stacks_project.Chap27.Lemma_27_8_7_AssociatedSheaf
import StacksCheckRecall

@[expose] public section

universe uA uσ

section

variable {A : Type uA} {σ : Type uσ} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 27.8.7 (1): the homogeneous spectrum of a graded ring, equipped with its canonical
structure sheaf, is the scheme `AlgebraicGeometry.Proj 𝒜`. -/
@[stacks 01MB] #check (AlgebraicGeometry.Proj 𝒜 : AlgebraicGeometry.Scheme)

/- Lemma 27.8.7 (2): every standard open attached to a positive-degree homogeneous element is
an affine open of `AlgebraicGeometry.Proj 𝒜`. -/
@[stacks 01MB] #check
  (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 :
    ∀ (f : A) {m : ℕ}, f ∈ 𝒜 m → 0 < m →
      AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.Proj.basicOpen 𝒜 f))

section

variable {M : Type uA} [AddCommGroup M] [Module A M]
variable (ℳ : ℤ → Submodule ℤ M) [DirectSum.Decomposition ℳ]
variable [SetLike.GradedSMul 𝒜 ℳ]

/- Lemma 27.8.7 (3): for every `ℤ`-graded `A`-module, the sheaf associated by
degree-zero homogeneous localization is quasi-coherent on `AlgebraicGeometry.Proj 𝒜`. -/
@[stacks 01MB] #check
  (AlgebraicGeometry.Proj.associatedSheaf_isQuasicoherent 𝒜 ℳ :
    (AlgebraicGeometry.Proj.associatedSheaf 𝒜 ℳ).IsQuasicoherent)

end

end
