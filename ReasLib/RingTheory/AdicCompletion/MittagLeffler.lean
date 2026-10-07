module

public import ReasLib.RingTheory.AdicCompletion.DirectSum
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex.Projective
public import ReasLib.RingTheory.Flatness.MittagLeffler.DirectSum

/-!
# Flat Mittag-Leffler adic completions

This file records flatness and the Mittag-Leffler property for the adic completion of a flat
module whose closed fiber is projective.
-/

@[expose] public section

universe u v

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a Noetherian ring complete along `I`, the `I`-adic completion of a flat module with
projective closed fiber is flat. -/
@[stacks 05DK "flatness of an adic completion with projective closed fiber"]
instance adicCompletion (I : Ideal R) [IsNoetherianRing R]
    [IsAdicComplete I R] [Module.Flat R M]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Flat R (AdicCompletion I M) := sorry

end Module.Flat

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a Noetherian ring complete along `I`, the `I`-adic completion of a flat module with
projective closed fiber is Mittag-Leffler. -/
@[stacks 05DK "Mittag-Leffler adic completion with projective closed fiber"]
instance adicCompletion (I : Ideal R) [IsNoetherianRing R]
    [IsAdicComplete I R] [Module.Flat R M]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.MittagLeffler R (AdicCompletion I M) := sorry

end Module.MittagLeffler
