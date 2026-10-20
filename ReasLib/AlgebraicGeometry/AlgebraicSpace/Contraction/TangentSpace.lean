module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.RimSchlessinger
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.TangentSpace

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The tangent space at a finite-type field-valued point of the contraction
functor is finite-dimensional over that field, with its canonical scalar action. -/
theorem finiteDimensional_tangentSpace (σ : ContractionSituation S)
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : σ.functor.obj (op (asLocallyNoetherian (Over.mk kToS)))) :
    -- Local instance justification (proof-local temporary data): the proved RS condition supplies the canonical H2 and tangent module instances only within this result type, without registering a companion instance for contraction data.
    letI : Scheme.Over.HasRimSchlessinger σ.functor := hasRimSchlessinger σ
    FiniteDimensional k (tangentSpace σ.functor openImmersion kToS h_factor x0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
