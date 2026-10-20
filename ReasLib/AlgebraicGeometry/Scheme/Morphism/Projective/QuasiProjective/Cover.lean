module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ProjectiveSpace

/-!
# Quasi-projective morphisms on open covers

This file relates local quasi-projectivity to H-quasi-projectivity after restriction to an open
cover of the target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A scheme morphism is locally quasi-projective exactly when it is H-quasi-projective after
restriction to every member of some open cover of its target. -/
theorem locallyQuasiProjective_iff_exists_openCover_hQuasiProjective
    (f : X ⟶ S) :
    LocallyQuasiProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S,
        ∀ i : 𝒰.I₀, HQuasiProjective (f ∣_ ((𝒰.f i).opensRange)) := sorry

end AlgebraicGeometry
