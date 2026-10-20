module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.TangentSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Over

universe u

/- Lemma 98.27.13: The tangent spaces of the contraction functor are
finite-dimensional over the finite-type residue field. -/
@[stacks 0GI7] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.finiteDimensional_tangentSpace :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S)
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : σ.functor.obj (op (asLocallyNoetherian (Over.mk kToS)))),
    -- Local instance justification (proof-local temporary data): the proved RS condition supplies the canonical H2 and tangent module instances only within this result type, without registering a companion instance for contraction data.
    letI : Scheme.Over.HasRimSchlessinger σ.functor := AlgebraicGeometry.AlgebraicSpace.ContractionSituation.hasRimSchlessinger σ
    FiniteDimensional k (tangentSpace σ.functor openImmersion kToS h_factor x0))
