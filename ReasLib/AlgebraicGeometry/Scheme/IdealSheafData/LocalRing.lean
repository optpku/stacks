module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

@[expose] public section

open TopCat.Presheaf

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The local ring of a closed subscheme at a point of its support. -/
noncomputable abbrev subschemeLocalRingAt {X : Scheme.{u}} (Y : X.IdealSheafData) (p : X)
    (hp : p ∈ Y.support) : CommRingCat :=
  let Z := Y.subscheme.toLocallyRingedSpace
  stalk Z.presheaf ⟨p, hp⟩

/-- The closed-subscheme local ring is the stalk at the corresponding supported point. -/
theorem subschemeLocalRingAt_def {X : Scheme.{u}} (Y : X.IdealSheafData) (p : X)
    (hp : p ∈ Y.support) :
    Y.subschemeLocalRingAt p hp =
      let Z := Y.subscheme.toLocallyRingedSpace
      stalk Z.presheaf ⟨p, hp⟩ := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
