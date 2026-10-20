module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.FiniteSet
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/- Exercise 111.37.8: for a graded ring `𝒜`, every finite set of points of `Proj 𝒜` is
contained in a standard affine open `D₊(f) = Proj.basicOpen 𝒜 f` for some homogeneous
element `f` of positive degree. -/
@[stacks 02A4] #check (AlgebraicGeometry.Proj.exists_basicOpen_containing_finiteSet :
  ∀ {A : Type u} {σ : Type v} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (E : Set (Proj 𝒜)), E.Finite →
    ∃ (d : ℕ) (hd : 0 < d) (f : A) (hf : f ∈ 𝒜 d), E ⊆ Proj.basicOpen 𝒜 f)
