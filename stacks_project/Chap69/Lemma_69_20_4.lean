module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.Graded
import StacksCheckRecall

/-! # Finiteness of graded cohomology over a Noetherian affine base -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.PullbackTilde
open AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology
open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.20.4: for a proper algebraic space over a Noetherian affine base, the cohomology
of a quasi-coherent finite-type graded module over the pullback affine tilde algebra is
finite over the graded algebra in every nonnegative cohomological degree. -/
@[stacks 08AT] #check (AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology.finite :
  ∀ {S : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    {X : AlgebraicSpace S} (σA : Spec (CommRingCat.of A) ⟶ S)
    (f : X ⟶ ofOver (Over.mk σA)) [Proper f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (𝓑 : ℤ → X.Modules)
    (pullbackData : Comparison 𝒜 σA f 𝓑) (F : GradedModule pullbackData.toOXGradedAlgebra)
    (hFQuasicoherent : ∀ n : ℤ, (F.obj n).IsQuasicoherent)
    (hFFiniteType : F.IsFiniteType) (p : ℕ),
    Module.FiniteWithAction B (carrier σA f F p) (module 𝒜 σA f pullbackData F p))
