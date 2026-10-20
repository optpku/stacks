module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Projective.LocalRing
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective.LocalRing
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective.Resolution
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Bounded.Projective

/-!
# Bounded free resolutions over local rings

This leaf is the local-ring converse to the projective-resolution view of bounded free
resolutions. It first converts the canonical bounded projective-resolution owner, then exposes
coordinate and finite-projective calculation bridges.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainComplex.FreeResolution

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a local ring, a canonical bounded projective resolution refines to a bounded free
resolution of the same module and length.

This is the primary local-ring bridge. Its input already owns the projective resolution witness,
so it neither chooses a resolution nor assumes Noetherianity or finiteness. The smallness
assumption is exactly the universe bridge from categorical to raw module projectivity. -/
@[stacks 0CXD "bounded projective resolutions over local rings are free"]
theorem HasLengthLE.ofProjectiveResolution
    {d : ℕ}
    (hM : CategoryTheory.ProjectiveResolution.HasLengthLE (ModuleCat.of R M) d) :
    HasLengthLE R M d := sorry

/-- Over a local ring, bounded free resolutions and canonical bounded projective resolutions are
equivalent presentations of the same length condition. -/
@[stacks 0CXD "free and canonical projective bounded resolutions over local rings"]
theorem HasLengthLE.iffProjectiveResolution
    (d : ℕ) :
    HasLengthLE R M d ↔
      CategoryTheory.ProjectiveResolution.HasLengthLE (ModuleCat.of R M) d := sorry

/-- Over a local ring, a bounded coordinate projective resolution refines to a bounded free
resolution of the same module and length.

This is the calculation-oriented companion to HasLengthLE.ofProjectiveResolution. It preserves the
coordinate presentation at the call site while delegating the structural conversion to the
canonical bounded-resolution owner. -/
@[stacks 0CXD "projective resolutions over local rings are free"]
theorem HasLengthLE.ofCoordinate
    {d : ℕ}
    (hM :
      ModuleCat.ProjectiveResolution.Coordinate.HasLengthLE
        (ModuleCat.of R M) d) :
    HasLengthLE R M d := sorry

/-- Over a local ring, bounded free resolutions and bounded coordinate projective resolutions are
equivalent presentations of the same length condition. -/
@[stacks 0CXD "free and projective bounded resolutions over local rings"]
theorem HasLengthLE.iffCoordinate
    (d : ℕ) :
    HasLengthLE R M d ↔
      ModuleCat.ProjectiveResolution.Coordinate.HasLengthLE
        (ModuleCat.of R M) d := sorry

/-- A projective-dimension bound over a local ring is equivalent to a bounded free resolution.

The smallness hypothesis supplies the canonical enough-projectives instance for ModuleCat and is
also exactly what is needed to convert categorical projectivity back to raw module projectivity. -/
@[stacks 0CXD "projective dimension and free resolutions over local rings"]
theorem hasProjectiveDimensionLE_iff_hasLengthLE
    (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔ HasLengthLE R M d := sorry

end ChainComplex.FreeResolution

namespace ChainComplex.FiniteFreeResolution

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a local ring, a bounded finite-projective resolution refines to a bounded finite free
resolution of the same module and length.

The finite-projective terms are carried by ModuleCat.FiniteProjective.HasResolutionLE. No ambient
Module.Finite assumption on the target is needed because the resolution witness supplies the
required finiteness. -/
@[stacks 0CXF "finite-projective resolutions over local rings are finite free"]
theorem HasLengthLE.ofFiniteProjectiveResolution
    {d : ℕ}
    (hM : ModuleCat.FiniteProjective.HasResolutionLE (ModuleCat.of R M) d) :
    HasLengthLE R M d := sorry

/-- For a finite module over a local Noetherian ring, a projective-dimension bound is equivalent
to the existence of a bounded finite free resolution.

This combines the Noetherian finite-projective-resolution criterion with the local-ring
finite-projective-to-finite-free conversion. -/
@[stacks 0CXF "projective dimension and finite free resolutions over local rings"]
theorem hasProjectiveDimensionLE_iff_hasLengthLE
    [IsNoetherianRing R] [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔ HasLengthLE R M d := sorry

end ChainComplex.FiniteFreeResolution
