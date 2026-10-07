module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.57.1

@stack 00JN
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain note: this item lies in graded commutative algebra and projective-spectrum topology.
It is a `core/canonical` recall: the owner abstraction is `ProjectiveSpectrum 𝒜`, while the
topology is derived canonically from that owner via `ProjectiveSpectrum.zariskiTopology`. No local
wrapper or parallel `Proj` point-space API is needed here. -/

/- Definition 10.57.1 (Stacks, Tag `00JN`) is recalled canonically by
`ProjectiveSpectrum 𝒜`: for an `ℕ`-graded commutative ring, its points are exactly the homogeneous
prime ideals that do not contain the irrelevant ideal. This is the source's `Proj(S)`. -/
@[stacks 00JN "homogeneous spectrum"]
#check @ProjectiveSpectrum

/- Companion recall: the topological-space structure on `ProjectiveSpectrum 𝒜` is the canonical
Zariski topology used for `Proj(S)`. -/
@[stacks 00JN "Proj Zariski topology"]
#check @ProjectiveSpectrum.zariskiTopology

end
