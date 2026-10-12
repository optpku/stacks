/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import stacks_project.Chap42.Remark_42_19_2_Pointwise
public import stacks_project.Chap42.Remark_42_8_2_Pointwise
public import stacks_project.Chap42.Remark_42_6_4_Milnor_K_theory_Boundary

/-!
# Pointwise primed Milnor complex

This file defines the primed product of degree-two Milnor K-groups of residue fields, the
tame-symbol boundary to the primed degree-one product, the Remark 42.19.2 boundary landed in
the primed degree-zero product, and the resulting three-term complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set Topology
open MilnorK.Coniveau

noncomputable section

universe u

namespace MilnorK.Coniveau

/-- On a locally Noetherian scheme, the canonical local ring of a specialization is
Noetherian. -/
instance instIsNoetherianRingSpecializationLocalRing_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] {x y : X} (h : x ⤳ y) :
    IsNoetherianRing (SpecializationLocalRing h) := sorry

end MilnorK.Coniveau

namespace AlgebraicGeometry.ChowGroup.Pointwise

variable {X : Scheme.{u}}

/-- The unrestricted product of degree-two Milnor K-groups of residue fields of
points of dimension `k`. -/
abbrev degreeTwoCoefficients (d : X → ℤ) (k : ℤ) : Type u :=
  (x : {x : X // d x = k}) → MilnorK.Group 2 (X.residueField x.1)

/-- Unfolding the unrestricted product of degree-two Milnor K-groups. -/
theorem degreeTwoCoefficients_eq (d : X → ℤ) (k : ℤ) :
    degreeTwoCoefficients d k =
      ((x : {x : X // d x = k}) → MilnorK.Group 2 (X.residueField x.1)) := sorry

/-- A family of `K₂ᴹ` coefficients is locally finite when every quasi-compact open of `X`
meets only finitely many nonzero terms. -/
def IsDegreeTwoLocallyFinite {d : X → ℤ} {k : ℤ} (n : degreeTwoCoefficients d k) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → {x | x.1 ∈ U ∧ n x ≠ 0}.Finite

/-- The primed sum is the subgroup of locally finite families in the unrestricted
product of `K₂ᴹ(κ(x))`. -/
def degreeTwoLocallyFinite (d : X → ℤ) (k : ℤ) : AddSubgroup (degreeTwoCoefficients d k) where
  carrier := {n | IsDegreeTwoLocallyFinite n}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the primed degree-two sum is local finiteness of the coefficient family. -/
theorem mem_degreeTwoLocallyFinite_iff {d : X → ℤ} {k : ℤ} (n : degreeTwoCoefficients d k) :
    n ∈ degreeTwoLocallyFinite d k ↔ IsDegreeTwoLocallyFinite n := sorry

/-- The primed degree-two product inherits an abelian group structure from the unrestricted
product. -/
instance (priority := 2000) instAddCommGroupDegreeTwoLocallyFinite (d : X → ℤ) (k : ℤ) :
    AddCommGroup (degreeTwoLocallyFinite d k) :=
  AddSubgroup.toAddCommGroup (degreeTwoLocallyFinite d k)

/-- A primed degree-two product is an additive monoid with zero. -/
instance (priority := 2000) instAddZeroDegreeTwoLocallyFinite (d : X → ℤ) (k : ℤ) :
    AddZero (degreeTwoLocallyFinite d k) :=
  (instAddCommGroupDegreeTwoLocallyFinite d k).toAddZero

/-- The tame residue `∂_{O_{W_x, y}} : K₂ᴹ(κ(x)) → K₁ᴹ(κ(y))` along an immediate
specialization, obtained from the degree-two tame symbol on the canonical local ring of
`x ⤳ y`. -/
def tameResidue [IsLocallyNoetherian X] {x y : X} (hxy : IsImmediateSpecialization x y) :
    MilnorK.Group 2 (X.residueField x) →+ MilnorK.Group 1 (X.residueField y) :=
  (MilnorK.mapGroup (specializationResidueFieldMap hxy) 1).comp
    (MilnorK.boundaryOneOnGroup (SpecializationLocalRing hxy.specializes)
      (X.residueField x) (specializationDimension_eq_one hxy))

/-- On a pure degree-two symbol, the tame residue is the image of the local tame symbol. -/
theorem tameResidue_symbol [IsLocallyNoetherian X] {x y : X}
    (hxy : IsImmediateSpecialization x y) (f g : (X.residueField x)ˣ) :
    tameResidue hxy (MilnorK.symbol ![f, g]) =
      MilnorK.mapGroup (specializationResidueFieldMap hxy) 1
        (MilnorK.degreeOneMap (IsLocalRing.ResidueField
            (SpecializationLocalRing hxy.specializes))
          (Additive.ofMul
            (TameSymbol.value (SpecializationLocalRing hxy.specializes)
              (X.residueField x) (specializationDimension_eq_one hxy) f g))) := sorry

variable [IsLocallyNoetherian X]
variable (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)

open Classical in
/-- The underlying coefficient family of the first primed Milnor boundary. -/
def firstBoundary_toFun (n : degreeTwoLocallyFinite d (k + 2)) :
    locallyFinite d (k + 1) :=
  ⟨fun y ↦ ∑ᶠ x : {x : X // d x = k + 2},
      if h : IsImmediateSpecialization x.1 y.1 then tameResidue h (n.1 x) else 0,
    sorry⟩

/-- The first differential of the primed Milnor complex, sending a locally finite family of
degree-two residue-field classes at dimension `k + 2` to the locally finite family of tame
residues along immediate specializations of dimension `k + 1`. -/
def firstBoundary : degreeTwoLocallyFinite d (k + 2) →+ locallyFinite d (k + 1) where
  toFun := firstBoundary_toFun d k
  map_zero' := sorry
  map_add' := sorry

open Classical in
/-- Evaluating the first primed Milnor boundary recovers the coefficientwise tame-residue
sum. -/
theorem firstBoundary_apply (n : degreeTwoLocallyFinite d (k + 2))
    (y : {y : X // d y = k + 1}) :
    (firstBoundary d k n).1 y =
      ∑ᶠ x : {x : X // d x = k + 2},
        if h : IsImmediateSpecialization x.1 y.1 then tameResidue h (n.1 x) else 0 := sorry

open Classical in
/-- A primed family supported at a single point of dimension `k + 2` is sent to the
corresponding family of tame residues. -/
theorem firstBoundary_of (x : X) (hx : d x = k + 2) (n : degreeTwoLocallyFinite d (k + 2))
    (hsupp : ∀ y : {y : X // d y = k + 2}, n.1 y ≠ 0 → y = ⟨x, hx⟩)
    (y : {y : X // d y = k + 1}) :
    (firstBoundary d k n).1 y =
      if h : IsImmediateSpecialization x y.1 then
        tameResidue h (n.1 ⟨x, hx⟩)
      else
        0 := sorry

/-- The second differential of the primed Milnor complex is the Remark 42.19.2 boundary,
landed in the primed `K₀ᴹ` product via the canonical identification of `Z_k(X)`. -/
def secondBoundary : locallyFinite d (k + 1) →+ CycleGroup.Pointwise.locallyFinite d k :=
  (CycleGroup.Pointwise.equiv d k).toAddMonoidHom.comp (boundaryHom d k)

/-- Evaluating the second primed Milnor boundary recovers the Remark 42.19.2 boundary
transported to primed `K₀ᴹ` coefficients. -/
theorem secondBoundary_apply (n : locallyFinite d (k + 1)) :
    secondBoundary d k n = CycleGroup.Pointwise.equiv d k (boundaryHom d k n) := sorry

/-- The composite of the two primed Milnor boundaries is zero. -/
theorem firstBoundary_comp_eq_zero :
    AddCommGrpCat.ofHom (firstBoundary d k) ≫
      AddCommGrpCat.ofHom (secondBoundary d k) = 0 := sorry

/-- The short complex `⊕'_{d(x)=k+2} K₂ᴹ(κ(x)) → ⊕'_{d(x)=k+1} K₁ᴹ(κ(x)) →
⊕'_{d(x)=k} K₀ᴹ(κ(x))`. -/
def milnorComplex : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (firstBoundary d k))
    (AddCommGrpCat.ofHom (secondBoundary d k)) (firstBoundary_comp_eq_zero d k)

/-- The first arrow of the primed Milnor complex is the tame-symbol boundary. -/
theorem milnorComplex_f : (milnorComplex d k).f = AddCommGrpCat.ofHom (firstBoundary d k) :=
  sorry

/-- The second arrow of the primed Milnor complex is the Remark 42.19.2 boundary landed in
primed `K₀ᴹ`. -/
theorem milnorComplex_g : (milnorComplex d k).g = AddCommGrpCat.ofHom (secondBoundary d k) :=
  sorry

end AlgebraicGeometry.ChowGroup.Pointwise
