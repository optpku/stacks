module

public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover

/-!
# Standard Zariski covers of affine opens

This leaf gives ambient-scheme views of the ring-level standard-cover owner
for the section ring of an affine open. It is independent of a choice of site
or Grothendieck topology.
-/

@[expose] public section

open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

namespace StandardZariskiCover

/-- A finite distinguished-open cover of one affine open, with arbitrary finite index type and
  ring-level data owned by `PrimeSpectrum.StandardOpenCoverOf`. -/
@[stacks 020T "standard cover of an affine open"]
abbrev OnAffineOpen (S : Scheme.{u}) (U : S.affineOpens) :
    Type (max u (v + 1)) :=
  PrimeSpectrum.StandardOpenCoverOf.{u, v} (1 : Γ(S, U))

namespace OnAffineOpen

variable {S : Scheme.{u}} {U : S.affineOpens}

/-- The finite index type of an affine-open standard Zariski cover. -/
@[stacks 020T "affine-open standard cover index"]
abbrev index (𝒰 : StandardZariskiCover.OnAffineOpen.{u, v} S U) : Type v :=
  PrimeSpectrum.StandardOpenCoverOf.index 𝒰

/-- The family of distinguished opens underlying an affine-open standard
Zariski cover. -/
@[stacks 020T "affine-open standard cover family"]
def opens (𝒰 : StandardZariskiCover.OnAffineOpen.{u, v} S U) : 𝒰.index → S.Opens :=
  fun i ↦ S.basicOpen (𝒰.generator i)

/-- Evaluation of the distinguished-open family underlying an affine-open
standard Zariski cover. -/
@[simp, stacks 020T "affine-open standard cover family evaluation"]
theorem opens_apply (𝒰 : StandardZariskiCover.OnAffineOpen.{u, v} S U)
    (i : 𝒰.index) :
    𝒰.opens i = S.basicOpen (𝒰.generator i) := sorry

/-- The `i`-th distinguished open of an affine-open standard Zariski cover,
packaged as an affine open of the ambient scheme. -/
@[stacks 020T "affine-open member of a standard Zariski cover"]
def affineOpen (𝒰 : StandardZariskiCover.OnAffineOpen.{u, v} S U)
    (i : 𝒰.index) : S.affineOpens :=
  S.affineBasicOpen (𝒰.generator i)

/-- The `i`-th affine-open standard cover member is contained in the affine
open being covered. -/
@[stacks 020T "affine-open standard cover containment"]
theorem affineOpen_le (𝒰 : StandardZariskiCover.OnAffineOpen.{u, v} S U)
    (i : 𝒰.index) :
    (𝒰.affineOpen i : S.Opens) ≤ (U : S.Opens) := sorry

/-- The underlying open of an affine-open standard-cover member is its
corresponding distinguished open. -/
@[simp, stacks 020T "affine-open standard cover coercion"]
theorem affineOpen_coe (𝒰 : StandardZariskiCover.OnAffineOpen.{u, v} S U)
    (i : 𝒰.index) :
    (𝒰.affineOpen i : S.Opens) = 𝒰.opens i := sorry

/-- The distinguished opens of an affine-open standard cover have supremum
equal to the affine open being covered. -/
@[stacks 020T "affine-open standard cover supremum"]
theorem iSup_eq (𝒰 : StandardZariskiCover.OnAffineOpen.{u, v} S U) :
    (⨆ i : 𝒰.index, 𝒰.opens i) = (U : S.Opens) := sorry

end OnAffineOpen

end StandardZariskiCover

end AlgebraicGeometry.Scheme
