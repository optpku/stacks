module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Every quasi-coherent module on `Spec (CommRingCat.of (R ⧸ I))` is isomorphic to
the pullback of a quasi-coherent module on `Spec R` along the canonical quotient
closed immersion. -/
theorem exists_isQuasicoherent_pullback_closedImmersion {R : CommRingCat.{u}} (I : Ideal R)
    (𝒢 : (Spec (CommRingCat.of (R ⧸ I))).Modules) [𝒢.IsQuasicoherent] :
    ∃ ℱ : (Spec R).Modules, ℱ.IsQuasicoherent ∧
      Nonempty ((pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj ℱ ≅ 𝒢) := sorry

end AlgebraicGeometry.Scheme.Modules
