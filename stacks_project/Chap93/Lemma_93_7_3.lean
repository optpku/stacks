module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra.Tangent
import StacksCheckRecall

@[expose] public section

open CategoryTheory Functor
open GradedAlgebra FiniteProjectiveGradedAlgebraCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (Λ)

/- Lemma 93.7.3 (1)
Infinitesimal automorphisms of the trivial graded deformation correspond uniquely to
homogeneous degree-zero derivations, by the map id + εD.
-/
@[stacks 0DVZ] #check
  (FiniteProjectiveGradedAlgebraCat.inf_bijective_homogeneousDerivations Λ :
    ∀ P : FiniteProjectiveGradedAlgebra k, Function.Bijective (idAddEpsilon Λ P))

/- Lemma 93.7.3 (2)
For a finitely generated locally finite graded algebra, the degree-zero derivations
form a finite-dimensional vector space.
-/
@[stacks 0DVZ] #check
  (GradedAlgebra.homogeneousDerivations_finiteDimensional :
    ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A]
      (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
      [∀ degree, FiniteDimensional k (𝒜 degree)] [Algebra.FiniteType k A],
      FiniteDimensional k (homogeneousDerivations 𝒜))

/- Lemma 93.7.3 (3)
The tangent space of the deformation category of a finitely generated locally finite
graded algebra is finite-dimensional.
-/
@[stacks 0DVZ] #check
  (FiniteProjectiveGradedAlgebraCat.tangentSpace_finiteDimensional Λ :
    ∀ (P : FiniteProjectiveGradedAlgebra k) [Algebra.FiniteType k P.carrier],
      FiniteDimensional k (tangentSpace (deformationForget Λ P)))
