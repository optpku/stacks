module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Subquotient

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An ℕ-indexed monotone chain of quasicoherent subobjects of a coherent module on a
Noetherian scheme is eventually constant. -/
theorem quasiCoherentSubobject_monotone_stabilizes
    {X : Scheme.{u}} [IsNoetherian X]
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (f : ℕ →o Subobject ℱ)
    (hf_qc : ∀ n : ℕ, (((f n : Subobject ℱ) : X.Modules)).IsQuasicoherent) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := sorry

end AlgebraicGeometry.Scheme.Modules
