module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

/-!
# Projective morphisms on open covers

This file relates local projectivity to H-projectivity after restriction to an open cover of the
target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A scheme morphism is locally projective exactly when it is H-projective after restriction to
every member of some open cover of its target. -/
theorem locallyProjective_iff_exists_openCover_hProjective
    (f : X ⟶ S) :
    LocallyProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S,
        ∀ i : 𝒰.I₀, HProjective (f ∣_ ((𝒰.f i).opensRange)) := sorry

end AlgebraicGeometry
