module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal
public import ReasLib.RingTheory.LocalRing.Length.ResidueImage

/-!
# Length over a classical deformation base

For a classical complete local base, passing between a local algebra and the base does not
change module length when their residue fields are compatibly identified.
-/

@[expose] public section

universe u v w

namespace IsLocalRing

/-- Over a classical complete local base, a module over a local algebra with the chosen
residue field has the same length over the algebra and over the base. -/
theorem length_eq_of_classical {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    [ArtinianLocalAlgCat.IsClassical Λ k]
    {A : Type v} [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (residueFieldIso : ResidueField A ≃ₐ[Λ] k) {M : Type w}
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M] :
    Module.length A M = Module.length Λ M := sorry

end IsLocalRing
