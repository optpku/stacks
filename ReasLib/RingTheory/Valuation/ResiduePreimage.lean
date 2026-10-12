/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Residue preimages of valuation subrings

Let `A` be a local ring and `V` a valuation subring of its residue field.  The
preimage of `V` under the residue map is a canonical subring of `A`.  The
construction is independent of a chosen presentation of `V` as the image of
another valuation ring; this is the reusable interface needed by residue
field arguments.
-/

universe u

namespace ValuationSubring

section Local

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-! ### The construction and its map -/

/-- The subring of a local ring whose residue classes lie in `V`. -/
@[stacks 088Z "residue preimage of a valuation subring"]
noncomputable def residuePreimage (V : ValuationSubring (IsLocalRing.ResidueField A)) :
    Subring A :=
  V.toSubring.comap (IsLocalRing.residue A)

/-- Membership in a residue preimage is exactly the corresponding residue-field membership. -/
@[simp, stacks 088Z "residue-preimage membership"]
theorem mem_residuePreimage_iff
    (V : ValuationSubring (IsLocalRing.ResidueField A)) (x : A) :
    x ∈ residuePreimage V ↔ IsLocalRing.residue A x ∈ V :=
  Iff.rfl

/-- The maximal ideal of the ambient local ring is contained in every residue preimage. -/
@[stacks 088Z "maximal-ideal elements in a residue preimage"]
theorem mem_residuePreimage_of_mem_maximalIdeal
    (V : ValuationSubring (IsLocalRing.ResidueField A)) {x : A}
    (hx : x ∈ IsLocalRing.maximalIdeal A) :
    x ∈ residuePreimage V := sorry

/-- The residue map with codomain restricted to the chosen valuation subring. -/
@[stacks 088Z "restricted residue map"]
noncomputable def residueMap
    (V : ValuationSubring (IsLocalRing.ResidueField A)) :
    residuePreimage V →+* V :=
  ((IsLocalRing.residue A).comp (residuePreimage V).subtype).codRestrict V
    (fun x => x.2)

/-- Coercion of the restricted residue map agrees with the ordinary residue map. -/
@[simp, stacks 088Z "restricted residue map application"]
theorem residueMap_apply
    (V : ValuationSubring (IsLocalRing.ResidueField A))
    (x : residuePreimage V) :
    (residueMap V x : IsLocalRing.ResidueField A) = IsLocalRing.residue A x :=
  rfl

/-! ### Locality and maximal ideals -/

/-- A residue preimage of a valuation subring is local. -/
instance residuePreimage.isLocalRing
    (V : ValuationSubring (IsLocalRing.ResidueField A)) :
    IsLocalRing (residuePreimage V) := sorry

/-- The maximal ideal of a residue preimage is the comap of the maximal ideal of `V`. -/
@[stacks 088Z "maximal ideal of a residue preimage"]
theorem maximalIdeal_residuePreimage
    (V : ValuationSubring (IsLocalRing.ResidueField A)) :
    IsLocalRing.maximalIdeal (residuePreimage V) =
      (IsLocalRing.maximalIdeal V).comap (residueMap V) := sorry

/-- The restricted residue map is a local ring homomorphism. -/
instance residueMap.isLocalHom
    (V : ValuationSubring (IsLocalRing.ResidueField A)) :
    IsLocalHom (residueMap V) := sorry

/-- The restricted residue map is surjective because the residue map of a local ring is. -/
@[stacks 088Z "surjectivity of the restricted residue map"]
theorem residueMap_surjective
    (V : ValuationSubring (IsLocalRing.ResidueField A)) :
    Function.Surjective (residueMap V) := sorry

/-- Elementwise form of the maximal-ideal comparison for a residue preimage. -/
@[simp, stacks 088Z "maximal-ideal membership in a residue preimage"]
theorem mem_maximalIdeal_residuePreimage_iff
    (V : ValuationSubring (IsLocalRing.ResidueField A))
    (x : residuePreimage V) :
    x ∈ IsLocalRing.maximalIdeal (residuePreimage V) ↔
      residueMap V x ∈ IsLocalRing.maximalIdeal V := sorry

end Local

/-! ### Valuation-ring inheritance -/

section Valuation

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]

/-- The residue preimage of a valuation subring in a valuation ring is a valuation ring. -/
@[stacks 088Z "valuation ring of a residue preimage"]
theorem residuePreimage_isValuationRing
    (V : ValuationSubring (IsLocalRing.ResidueField A)) :
    ValuationRing (residuePreimage V) := sorry

end Valuation

end ValuationSubring
