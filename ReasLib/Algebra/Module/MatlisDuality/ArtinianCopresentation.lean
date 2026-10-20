module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Module.Injective.ResidueField
public import ReasLib.Algebra.Module.MatlisDuality.InjectiveHullArtinian

@[expose] public section

universe u v w

namespace LinearMap.IsInjectiveHull

/-- For a module over a Noetherian local ring and a chosen injective hull of its residue
field, Artinianity, maximal-ideal torsion with finite socle, and finite injective
copresentation are equivalent. -/
theorem artinianModule_tfae
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull)
    (M : Type w) [AddCommGroup M] [Module R M] :
    List.TFAE
      [ IsArtinian R M
      , Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal R) M ∧
          Module.Finite (IsLocalRing.ResidueField R)
            (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R))
      , ∃ n m : ℕ, ∃ f : M →ₗ[R] (Fin n → E),
          ∃ g : (Fin n → E) →ₗ[R] (Fin m → E),
            Function.Injective f ∧ Function.Exact f g
      ] := sorry

end LinearMap.IsInjectiveHull
