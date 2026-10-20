module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pointwise
public import ReasLib.AlgebraicGeometry.MilnorK.Coniveau

/-!
# Locally finite Milnor complexes

Locally finite families of residue-field Milnor classes in degrees two, one, and zero
form a complex with the tame-symbol and principal-divisor boundaries.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set Topology
open MilnorK.Coniveau

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Pointwise

variable {X : Scheme.{u}}

/-- The unrestricted product of degree-two Milnor K-groups of residue fields of
points of dimension `k`. -/
abbrev degreeTwoCoefficients (d : X → ℤ) (k : ℤ) : Type u :=
  (x : {x : X // d x = k}) → MilnorK.Group 2 (X.residueField x.1)

/-- A family of `K₂ᴹ` coefficients is locally finite when every quasi-compact open of `X`
meets only finitely many nonzero terms. -/
def IsDegreeTwoLocallyFinite {d : X → ℤ} {k : ℤ} (n : degreeTwoCoefficients d k) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → {x | x.1 ∈ U ∧ n x ≠ 0}.Finite

/-- The zero degree-two coefficient family is locally finite. -/
private theorem zero_isDegreeTwoLocallyFinite (d : X → ℤ) (k : ℤ) :
    IsDegreeTwoLocallyFinite (0 : degreeTwoCoefficients d k) := sorry

/-- Addition preserves local finiteness of degree-two coefficient families. -/
private theorem add_isDegreeTwoLocallyFinite {d : X → ℤ} {k : ℤ}
    {a b : degreeTwoCoefficients d k}
    (ha : IsDegreeTwoLocallyFinite a) (hb : IsDegreeTwoLocallyFinite b) :
    IsDegreeTwoLocallyFinite (a + b) := sorry

/-- Negation preserves local finiteness of degree-two coefficient families. -/
private theorem neg_isDegreeTwoLocallyFinite {d : X → ℤ} {k : ℤ}
    {a : degreeTwoCoefficients d k} (ha : IsDegreeTwoLocallyFinite a) :
    IsDegreeTwoLocallyFinite (-a) := sorry

/-- The primed sum is the subgroup of locally finite families in the unrestricted
product of `K₂ᴹ(κ(x))`. -/
@[reducible, no_expose] def degreeTwoLocallyFinite (d : X → ℤ) (k : ℤ) :
    AddSubgroup (degreeTwoCoefficients d k) where
  carrier := {n | IsDegreeTwoLocallyFinite n}
  zero_mem' := zero_isDegreeTwoLocallyFinite d k
  add_mem' := add_isDegreeTwoLocallyFinite
  neg_mem' := neg_isDegreeTwoLocallyFinite

/-- Membership in the primed degree-two sum is local finiteness of the coefficient family. -/
theorem mem_degreeTwoLocallyFinite_iff {d : X → ℤ} {k : ℤ} (n : degreeTwoCoefficients d k) :
    n ∈ degreeTwoLocallyFinite d k ↔ IsDegreeTwoLocallyFinite n := Iff.rfl

variable [IsLocallyNoetherian X]
variable (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)

open Classical in
/-- Only finitely many degree-two coefficients contribute a nonzero residue at a fixed point. -/
private theorem firstBoundary_finiteSupport (n : degreeTwoLocallyFinite d (k + 2))
    (y : {y : X // d y = k + 1}) :
    (Function.support (fun x : {x : X // d x = k + 2} ↦
      if h : IsImmediateSpecialization x.1 y.1 then degreeOneResidue h (n.1 x) else 0)).Finite := sorry

open Classical in
/-- The coefficientwise sum of tame residues of a locally finite family is locally finite. -/
private theorem firstBoundary_isLocallyFinite (n : degreeTwoLocallyFinite d (k + 2)) :
    IsLocallyFinite (fun y : {y : X // d y = k + 1} ↦
      ∑ᶠ x : {x : X // d x = k + 2},
        if h : IsImmediateSpecialization x.1 y.1 then degreeOneResidue h (n.1 x) else 0) := sorry

open Classical in
/-- The underlying coefficient family of the first primed Milnor boundary. -/
@[no_expose] private def firstBoundary_toFun (n : degreeTwoLocallyFinite d (k + 2)) :
    locallyFinite d (k + 1) :=
  ⟨fun y ↦ ∑ᶠ x : {x : X // d x = k + 2},
      if h : IsImmediateSpecialization x.1 y.1 then degreeOneResidue h (n.1 x) else 0,
    (mem_locallyFinite_iff _).mpr (firstBoundary_isLocallyFinite d k n)⟩

/-- The coefficientwise tame-residue sum sends zero to zero. -/
private theorem firstBoundary_map_zero :
    firstBoundary_toFun d k 0 = 0 := sorry

/-- The coefficientwise tame-residue sum preserves addition. -/
private theorem firstBoundary_map_add (a b : degreeTwoLocallyFinite d (k + 2)) :
    firstBoundary_toFun d k (a + b) =
      firstBoundary_toFun d k a + firstBoundary_toFun d k b := sorry

/-- The first differential of the primed Milnor complex, sending a locally finite family of
degree-two residue-field classes at dimension `k + 2` to the locally finite family of tame
residues along immediate specializations of dimension `k + 1`. -/
@[no_expose] def firstBoundary : degreeTwoLocallyFinite d (k + 2) →+ locallyFinite d (k + 1) where
  toFun := firstBoundary_toFun d k
  map_zero' := firstBoundary_map_zero d k
  map_add' := firstBoundary_map_add d k

open Classical in
/-- Evaluating the first primed Milnor boundary recovers the coefficientwise tame-residue
sum. -/
theorem firstBoundary_apply (n : degreeTwoLocallyFinite d (k + 2))
    (y : {y : X // d y = k + 1}) :
    (firstBoundary d k n).1 y =
      ∑ᶠ x : {x : X // d x = k + 2},
        if h : IsImmediateSpecialization x.1 y.1 then degreeOneResidue h (n.1 x) else 0 := by rfl

open Classical in
/-- A primed family supported at a single point of dimension `k + 2` is sent to the
corresponding family of tame residues. -/
theorem firstBoundary_of (x : X) (hx : d x = k + 2) (n : degreeTwoLocallyFinite d (k + 2))
    (hsupp : ∀ y : {y : X // d y = k + 2}, n.1 y ≠ 0 → y = ⟨x, hx⟩)
    (y : {y : X // d y = k + 1}) :
    (firstBoundary d k n).1 y =
      if h : IsImmediateSpecialization x y.1 then
        degreeOneResidue h (n.1 ⟨x, hx⟩)
      else
        0 := sorry

/-- The second differential of the primed Milnor complex is the principal-divisor boundary,
landed in the primed `K₀ᴹ` product via the canonical identification of `Z_k(X)`. -/
def secondBoundary : locallyFinite d (k + 1) →+ CycleGroup.Pointwise.locallyFinite d k :=
  (CycleGroup.Pointwise.equiv d k).toAddMonoidHom.comp (boundaryHom d k)

/-- Evaluating the second primed Milnor boundary recovers the principal-divisor boundary
transported to primed `K₀ᴹ` coefficients. -/
theorem secondBoundary_apply (n : locallyFinite d (k + 1)) :
    secondBoundary d k n = CycleGroup.Pointwise.equiv d k (boundaryHom d k n) := rfl

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
theorem milnorComplex_f : (milnorComplex d k).f = AddCommGrpCat.ofHom (firstBoundary d k) := rfl

/-- The second arrow of the primed Milnor complex is the principal-divisor boundary landed in
primed `K₀ᴹ`. -/
theorem milnorComplex_g : (milnorComplex d k).g = AddCommGrpCat.ofHom (secondBoundary d k) := rfl

end AlgebraicGeometry.ChowGroup.Pointwise

namespace AlgebraicGeometry.ChowGroup

/-- The locally finite Milnor complex of a scheme locally of finite type over a universally
catenary base, indexed by the induced relative dimension function. -/
noncomputable def milnorComplex {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    ShortComplex Ab :=
  @Pointwise.milnorComplex X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k

/-- The relative Milnor complex is the pointwise complex of the relative dimension function. -/
theorem milnorComplex_eq {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    milnorComplex p δ k =
      @Pointwise.milnorComplex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k := rfl

end AlgebraicGeometry.ChowGroup
