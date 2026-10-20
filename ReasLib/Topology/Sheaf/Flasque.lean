module

public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Flasque sheaves

This module is the ReasLib import surface for Mathlib's canonical `TopCat.Sheaf.IsFlasque` API used
by the Stacks Project formalization.

Mathlib already owns the basic flasque API, which is reused rather than restated here:
- `TopCat.Sheaf.IsFlasque.pushforward_isFlasque`: pushforward preserves flasqueness;
- `TopCat.Sheaf.IsFlasque.epi_of_shortExact`: for a short exact sequence `0 → F → G → H → 0` of
  abelian sheaves with `F` flasque, `G(U) → H(U)` is surjective;
- `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`: if `F` and `G` are flasque, so is `H`.

The Stacks injective-to-flasque statement is owned by the ringed-space module API, where its
module structure is part of the source hypothesis.  This module therefore adds no parallel
set-valued theorem; consumers should use the canonical declarations above or the appropriate
module-valued owner.

## References

- [Stacks Project, Tag 09SV](https://stacks.math.columbia.edu/tag/09SV)
- [Hartshorne, Algebraic Geometry, II.2]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

noncomputable section

universe w v u

namespace TopCat.Sheaf.Flasque

variable {X : TopCat.{w}}

end TopCat.Sheaf.Flasque

end

end
