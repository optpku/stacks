module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Flat

/-- A flat, quasi-compact, surjective monomorphism of schemes is an isomorphism. -/
theorem isIso_of_quasiCompact_surjective_mono {X Y : Scheme} (f : X ⟶ Y)
    [Flat f] [QuasiCompact f] [Surjective f] [Mono f] : IsIso f := sorry

end AlgebraicGeometry.Flat
