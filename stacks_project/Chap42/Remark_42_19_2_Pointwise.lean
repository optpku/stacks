module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.GenericPoint
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.FunctionField
public import stacks_project.Chap42.Remark_42_8_2_Pointwise

/-!
# Pointwise K₁ presentation of Chow groups

This file defines the primed product of degree-one Milnor K-groups of residue fields, the
boundary map sending a locally finite family to the corresponding sum of pushed-forward
principal cycles, and the resulting short complex with Chow groups.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Pointwise

variable {X : Scheme.{u}}

/-- The unrestricted product of degree-one Milnor K-groups of residue fields of
points of dimension `k`. -/
abbrev degreeOneCoefficients (d : X → ℤ) (k : ℤ) : Type u :=
  (x : {x : X // d x = k}) → MilnorK.Group 1 (X.residueField x.1)

/-- Unfolding the unrestricted product of degree-one Milnor K-groups. -/
theorem degreeOneCoefficients_eq (d : X → ℤ) (k : ℤ) :
    degreeOneCoefficients d k =
      ((x : {x : X // d x = k}) → MilnorK.Group 1 (X.residueField x.1)) := sorry

/-- A family of `K₁ᴹ` coefficients is locally finite when every quasi-compact open of `X`
meets only finitely many nonzero terms. -/
def IsLocallyFinite {d : X → ℤ} {k : ℤ} (n : degreeOneCoefficients d k) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → {x | x.1 ∈ U ∧ n x ≠ 0}.Finite

/-- The primed sum is the subgroup of locally finite families in the unrestricted
product of `K₁ᴹ(κ(x))`. -/
def locallyFinite (d : X → ℤ) (k : ℤ) : AddSubgroup (degreeOneCoefficients d k) where
  carrier := {n | IsLocallyFinite n}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the primed degree-one sum is local finiteness of the coefficient family. -/
theorem mem_locallyFinite_iff {d : X → ℤ} {k : ℤ} (n : degreeOneCoefficients d k) :
    n ∈ locallyFinite d k ↔ IsLocallyFinite n := sorry

/-- The primed degree-one product inherits an abelian group structure from the unrestricted
product. -/
instance (priority := 2000) instAddCommGroupLocallyFinite (d : X → ℤ) (k : ℤ) :
    AddCommGroup (locallyFinite d k) :=
  AddSubgroup.toAddCommGroup (locallyFinite d k)

/-- A primed degree-one product is an additive monoid with zero. -/
instance (priority := 2000) instAddZeroLocallyFinite (d : X → ℤ) (k : ℤ) :
    AddZero (locallyFinite d k) :=
  (instAddCommGroupLocallyFinite d k).toAddZero

/-- The canonical field homomorphism from `κ(x)` to the function field of the reduced
closure of `x`. -/
def residueFieldToFunctionField (x : X) :
    X.residueField x →+* (Scheme.PointClosure.scheme x).functionField :=
  let W := Scheme.PointClosure.scheme x
  let η := genericPoint W
  (Scheme.functionFieldResidueEquiv W).symm.toRingHom.comp
    ((X.residueFieldCongr (Scheme.PointClosure.ι_map_genericPoint x).symm).hom ≫
      (Scheme.PointClosure.ι x).residueFieldMap η).hom

/-- The canonical map `κ(x) → R(W_x)` is bijective. -/
theorem residueFieldToFunctionField_bijective (x : X) :
    Function.Bijective (residueFieldToFunctionField x) := sorry

/-- Transport of a degree-one Milnor K-class in `κ(x)` to a unit in the function field
of the reduced closure of `x`. -/
def toFunctionFieldUnits (x : X) (ξ : MilnorK.Group 1 (X.residueField x)) :
    (Scheme.PointClosure.scheme x).functionFieldˣ :=
  Units.map (residueFieldToFunctionField x).toMonoidHom
    (Additive.toMul ((MilnorK.degreeOneEquiv (X.residueField x)).symm ξ))

/-- Transport of `K₁ᴹ(κ(x))` recovers the image of the corresponding residue-field unit. -/
theorem toFunctionFieldUnits_spec (x : X) (a : (X.residueField x)ˣ) :
    toFunctionFieldUnits x (MilnorK.degreeOneMap (X.residueField x) (Additive.ofMul a)) =
      Units.map (residueFieldToFunctionField x).toMonoidHom a := sorry

/-- The reduced closures of the nonzero support of a primed degree-one family are
locally finite. -/
theorem locallyFinite_closedSubset {d : X → ℤ} {m : ℤ} (n : locallyFinite d m) :
    LocallyFinite fun j : {x : {x : X // d x = m} // n.1 x ≠ 0} ↦
      (Scheme.PointClosure.closedSubset j.1.1 : Set X) := sorry

variable [IsLocallyNoetherian X]
variable (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)

/-- The underlying map of `∂` on a primed degree-one family. -/
def boundaryHom_toFun (n : locallyFinite d (k + 1)) : CycleGroup X d k :=
  RationalEquivalence.boundary d k
    (fun j : {x : {x : X // d x = k + 1} // n.1 x ≠ 0} ↦ j.1.1)
    (fun j ↦ j.1.2)
    (fun j ↦ toFunctionFieldUnits j.1.1 (n.1 j.1))
    (locallyFinite_closedSubset n)

/-- The boundary `∂` sends a locally finite family of degree-one residue-field classes
at dimension `k + 1` to the corresponding locally finite sum of pushed-forward principal
cycles in `Z_k(X)`. -/
def boundaryHom : locallyFinite d (k + 1) →+ CycleGroup X d k where
  toFun := boundaryHom_toFun d k
  map_zero' := sorry
  map_add' := sorry

/-- Evaluating `∂` recovers the locally finite principal-cycle sum. -/
theorem boundaryHom_apply (n : locallyFinite d (k + 1)) :
    boundaryHom d k n = boundaryHom_toFun d k n := sorry

/-- A primed family supported at a single point of dimension `k + 1` is sent to the
corresponding pushed-forward principal cycle. -/
theorem boundaryHom_principal (x : X) (hx : d x = k + 1) (n : locallyFinite d (k + 1))
    (hsupp : ∀ y : {y : X // d y = k + 1}, n.1 y ≠ 0 → y = ⟨x, hx⟩) :
    boundaryHom d k n =
      RationalEquivalence.principal d k x hx (toFunctionFieldUnits x (n.1 ⟨x, hx⟩)) := sorry

/-- The image of `∂` is the subgroup of rationally trivial degree-`k` cycles. -/
theorem range_eq_boundaries :
    (boundaryHom d k).range = RationalEquivalence.boundaries d k := sorry

/-- The composite of `∂` with the quotient map to Chow groups is zero. -/
theorem boundaryHom_comp_chowClass :
    AddCommGrpCat.ofHom (boundaryHom d k) ≫ AddCommGrpCat.ofHom (chowClass d k) = 0 := sorry

/-- The short complex `⊕'_{δ(x)=k+1} K₁ᴹ(κ(x)) → Z_k(X) → CH_k(X)`. -/
def complex : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (boundaryHom d k))
    (AddCommGrpCat.ofHom (chowClass d k)) (boundaryHom_comp_chowClass d k)

/-- The first arrow of the pointwise presentation complex is `∂`. -/
theorem complex_f : (complex d k).f = AddCommGrpCat.ofHom (boundaryHom d k) := sorry

/-- The second arrow of the pointwise presentation complex is the Chow class map. -/
theorem complex_g : (complex d k).g = AddCommGrpCat.ofHom (chowClass d k) := sorry

end AlgebraicGeometry.ChowGroup.Pointwise
