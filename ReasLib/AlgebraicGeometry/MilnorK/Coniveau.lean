/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.KTheory.Milnor.Norm
public import ReasLib.AlgebraicGeometry.Scheme.Excellent.Stalk
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.RingTheory.LocalRing.TameSymbol.Reciprocity
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField

@[expose] public section

noncomputable section

open AlgebraicGeometry
open scoped BigOperators DirectSum
open Classical

universe u v w

namespace MilnorK.Coniveau

/-- The canonical map from the stalk at a specialization point to the residue field at its
generization. -/
def specializationToResidue {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    X.presheaf.stalk y →+* X.residueField x :=
  (X.residue x).hom.comp (X.presheaf.stalkSpecializes h).hom

/-- The canonical local domain attached to a specialization `x ⤳ y`: the
stalk at `y`, modulo the kernel of its map to `κ(x)`. -/
abbrev SpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :=
  X.presheaf.stalk y ⧸ RingHom.ker (specializationToResidue h)

/-- The specialization quotient is an algebra in the residue field of the generization. -/
instance instAlgebraSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    Algebra (SpecializationLocalRing h) (X.residueField x) :=
  (Ideal.Quotient.lift (RingHom.ker (specializationToResidue h))
    (specializationToResidue h) fun _ ha ↦ ha).toAlgebra

/-- A specialization quotient is a domain. -/
instance instIsDomainSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    IsDomain (SpecializationLocalRing h) := sorry

/-- A specialization quotient is local. -/
instance instIsLocalRingSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    IsLocalRing (SpecializationLocalRing h) := sorry

/-- On a locally Noetherian scheme, a specialization quotient is Noetherian. -/
instance instIsNoetherianRingSpecializationLocalRing
    {X : Scheme.{u}} [IsLocallyNoetherian X] {x y : X} (h : x ⤳ y) :
    IsNoetherianRing (SpecializationLocalRing h) := sorry

/-- The residue field of the generization is the fraction field of the specialization
quotient. -/
instance instIsFractionRingSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    IsFractionRing (SpecializationLocalRing h) (X.residueField x) := sorry

/-- Excellence of the stalk makes a specialization quotient excellent. -/
instance instIsExcellentRingSpecializationLocalRing {X : Scheme.{u}} {x y : X}
    [IsExcellentRing.{u, u} (X.presheaf.stalk y)] (h : x ⤳ y) :
    IsExcellentRing.{u, u} (SpecializationLocalRing h) := sorry

/-- An immediate specialization has local dimension one. -/
theorem specializationDimension_eq_one {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    ringKrullDim (SpecializationLocalRing hxy.specializes) = 1 := sorry

/-- The specialization kernel lies in the kernel of the residue map at the target. -/
private theorem specializationResidueHom_ker {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    RingHom.ker (specializationToResidue hxy.specializes) ≤
      RingHom.ker (X.residue y).hom := sorry

/-- The residue map of an immediate specialization quotient toward `κ(y)`. -/
@[no_expose] noncomputable def specializationResidueHom {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    SpecializationLocalRing hxy.specializes →+* X.residueField y :=
  Ideal.Quotient.lift (RingHom.ker (specializationToResidue hxy.specializes))
    (X.residue y).hom (specializationResidueHom_ker hxy)

/-- The residue map of an immediate specialization quotient is local. -/
instance instIsLocalHomSpecializationResidueHom {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    IsLocalHom (specializationResidueHom hxy) := sorry

/-- The induced map of residue fields identifying the specialization quotient with `κ(y)`. -/
noncomputable def specializationResidueFieldMap {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    IsLocalRing.ResidueField (SpecializationLocalRing hxy.specializes) →+*
      X.residueField y :=
  IsLocalRing.ResidueField.lift (specializationResidueHom hxy)

/-- The residue-field map of an immediate specialization is bijective. -/
theorem specializationResidueFieldMap_bijective {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    Function.Bijective (specializationResidueFieldMap hxy) := sorry

/-- Branchwise higher Milnor transfers along residue extensions of immediate specializations
of an excellent Noetherian scheme. -/
abbrev SpecializationTransfers (X : Scheme.{u}) [IsNoetherian X]
    [Scheme.Excellent X] :=
  ∀ {x y : X} (hxy : IsImmediateSpecialization x y),
    (b : NormalizationBranch (SpecializationLocalRing hxy.specializes) (X.residueField x)) →
      NormalizationResidueTransfer (SpecializationLocalRing hxy.specializes)
        (X.residueField x) b

/-- The Milnor K-group direct sum over the points of dimension `j`. -/
abbrev Term (X : Scheme.{u}) (δ : X → ℤ) (i : ℕ) (j : ℤ) :=
  ⨁ x : {x : X // δ x = j}, Group i (X.residueField x.1)

/-- The coniveau term is the direct sum of the indicated residue-field Milnor K-groups. -/
theorem term_def (X : Scheme.{u}) (δ : X → ℤ) (i : ℕ) (j : ℤ) :
    Term X δ i j = (⨁ x : {x : X // δ x = j}, Group i (X.residueField x.1)) := sorry

/-- The canonical inclusion of one residue-field summand into a coniveau term. -/
noncomputable def termOf {X : Scheme.{u}} {δ : X → ℤ} {i : ℕ} {j : ℤ}
    (x : {x : X // δ x = j}) :
    Group i (X.residueField x.1) →+ Term X δ i j :=
  @DirectSum.of _ (fun y : {y : X // δ y = j} ↦ Group i (X.residueField y.1)) _
    (Classical.decEq _) x

/-- Evaluating the canonical summand inclusion at its own index recovers the original class. -/
theorem termOf_eq_same {X : Scheme.{u}} {δ : X → ℤ} {i : ℕ} {j : ℤ}
    (x : {x : X // δ x = j}) (a : Group i (X.residueField x.1)) :
    termOf x a x = a := sorry

/-- The excellent local residue `Kᵐ_{i+1}(κ(x)) →+ Kᵐ_i(κ(y))` along an immediate
specialization, using the supplied branchwise transfers. -/
noncomputable def excellentResidue {X : Scheme.{u}} [IsNoetherian X]
    [Scheme.Excellent X] {x y : X}
    (hxy : IsImmediateSpecialization x y)
    (N : (b : NormalizationBranch (SpecializationLocalRing hxy.specializes) (X.residueField x)) →
      NormalizationResidueTransfer (SpecializationLocalRing hxy.specializes)
        (X.residueField x) b)
    (i : ℕ) :
    Group (i + 1) (X.residueField x) →+ Group i (X.residueField y) :=
  (mapGroup (specializationResidueFieldMap hxy) i).comp
    (excellentLocalBoundary (SpecializationLocalRing hxy.specializes)
      (X.residueField x) (specializationDimension_eq_one hxy) N i)

/-- The preceding-degree excellent residue along the same immediate specialization. -/
noncomputable def excellentResiduePrev {X : Scheme.{u}} [IsNoetherian X]
    [Scheme.Excellent X] {x y : X}
    (hxy : IsImmediateSpecialization x y)
    (N : (b : NormalizationBranch (SpecializationLocalRing hxy.specializes) (X.residueField x)) →
      NormalizationResidueTransfer (SpecializationLocalRing hxy.specializes)
        (X.residueField x) b)
    (i : ℕ) (hi : 1 ≤ i) :
    Group i (X.residueField x) →+ Group (i - 1) (X.residueField y) :=
  (Nat.sub_add_cancel hi).symm ▸ excellentResidue hxy N (i - 1)

/-- Local components of the first excellent coniveau arrow: the excellent residue on incident
pairs, and zero otherwise. -/
noncomputable def excellentFirstLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j}) :
    Group (i + 1) (X.residueField x.1) →+ Group i (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then
    excellentResidue hxy (transfers hxy) i
  else
    0

/-- Local components of the second excellent coniveau arrow. -/
noncomputable def excellentSecondLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1}) :
    Group i (X.residueField x.1) →+ Group (i - 1) (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then
    excellentResiduePrev hxy (transfers hxy) i hi
  else
    0

/-- On an immediate specialization, the first local component is the excellent residue. -/
theorem excellentFirstLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    excellentFirstLocal δ transfers i j x y =
      excellentResidue hxy (transfers hxy) i := sorry

/-- On an immediate specialization, the second local component is the preceding excellent
residue. -/
theorem excellentSecondLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    excellentSecondLocal δ transfers i hi j x y =
      excellentResiduePrev hxy (transfers hxy) i hi := sorry

/-- The nonzero local residues of a fixed Milnor class have finite support. -/
theorem excellentFirstLocal_finiteSupport {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1})
    (a : Group (i + 1) (X.residueField x.1)) :
    {y : {y : X // δ y = j} | excellentFirstLocal δ transfers i j x y a ≠ 0}.Finite := sorry

/-- The sum of local residues sends zero to zero. -/
private theorem excellentFirst_map_zero {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) :
    (∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y 0)) = 0 := sorry

/-- The sum of local residues preserves addition. -/
private theorem excellentFirst_map_add {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1})
    (a b : Group (i + 1) (X.residueField x.1)) :
    (∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y (a + b))) =
      (∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y a)) +
        (∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y b)) := sorry

/-- The first coniveau arrow assembled from excellent local residues. -/
@[no_expose] noncomputable def excellentFirst {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ) :
    Term X δ (i + 1) (j + 1) →+ Term X δ i j :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y a)
        map_zero' := excellentFirst_map_zero δ transfers i j x
        map_add' := excellentFirst_map_add δ transfers i j x }

/-- The nonzero local residues of a fixed Milnor class have finite support. -/
theorem excellentSecondLocal_finiteSupport {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j})
    (a : Group i (X.residueField x.1)) :
    {y : {y : X // δ y = j - 1} | excellentSecondLocal δ transfers i hi j x y a ≠ 0}.Finite := sorry

/-- The sum of local residues sends zero to zero. -/
private theorem excellentSecond_map_zero {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j}) :
    (∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y 0)) = 0 := sorry

/-- The sum of local residues preserves addition. -/
private theorem excellentSecond_map_add {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j})
    (a b : Group i (X.residueField x.1)) :
    (∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y (a + b))) =
      (∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y a)) +
        (∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y b)) := sorry

/-- The second coniveau arrow assembled from excellent local residues. -/
@[no_expose] noncomputable def excellentSecond {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ) :
    Term X δ i j →+ Term X δ (i - 1) (j - 1) :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y a)
        map_zero' := excellentSecond_map_zero δ transfers i hi j x
        map_add' := excellentSecond_map_add δ transfers i hi j x }

/-- Evaluating the first excellent arrow on a homogeneous summand is the corresponding local
residue sum. -/
theorem excellentFirst_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) (a : Group (i + 1) (X.residueField x.1)) :
    excellentFirst δ transfers i j (termOf x a) =
      ∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y a) := sorry

/-- Evaluating the second excellent arrow on a homogeneous summand is the corresponding local
residue sum. -/
theorem excellentSecond_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j}) (a : Group i (X.residueField x.1)) :
    excellentSecond δ transfers i hi j (termOf x a) =
      ∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y a) := sorry

/-- The degree-one residue along an immediate specialization, using the concrete tame symbol. -/
noncomputable def degreeOneResidue {X : Scheme.{u}} [IsLocallyNoetherian X] {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    Group 2 (X.residueField x) →+ Group 1 (X.residueField y) :=
  (mapGroup (specializationResidueFieldMap hxy) 1).comp
    (boundaryOneOnGroup (SpecializationLocalRing hxy.specializes)
      (X.residueField x) (specializationDimension_eq_one hxy))

/-- On a pure degree-two symbol, the tame residue is the image of the local tame symbol. -/
theorem degreeOneResidue_symbol {X : Scheme.{u}} [IsLocallyNoetherian X] {x y : X}
    (hxy : IsImmediateSpecialization x y) (f g : (X.residueField x)ˣ) :
    degreeOneResidue hxy (MilnorK.symbol ![f, g]) =
      MilnorK.mapGroup (specializationResidueFieldMap hxy) 1
        (MilnorK.degreeOneMap (IsLocalRing.ResidueField
            (SpecializationLocalRing hxy.specializes))
          (Additive.ofMul
            (TameSymbol.value (SpecializationLocalRing hxy.specializes)
              (X.residueField x) (specializationDimension_eq_one hxy) f g))) := sorry

/-- The degree-zero residue along an immediate specialization, using the divisor valuation. -/
noncomputable def degreeZeroResidue {X : Scheme.{u}} [IsNoetherian X] {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    Group 1 (X.residueField x) →+ Group 0 (X.residueField y) :=
  (mapGroup (specializationResidueFieldMap hxy) 0).comp
    (divisorOrderOnGroup (SpecializationLocalRing hxy.specializes)
      (X.residueField x) (specializationDimension_eq_one hxy))

/-- Local components of the first degree-one coniveau arrow. -/
noncomputable def degreeOneFirstLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j}) :
    Group 2 (X.residueField x.1) →+ Group 1 (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then degreeOneResidue hxy else 0

/-- Local components of the second degree-one coniveau arrow. -/
noncomputable def degreeOneSecondLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1}) :
    Group 1 (X.residueField x.1) →+ Group 0 (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then degreeZeroResidue hxy else 0

/-- On an immediate specialization, the first degree-one local component is the tame symbol. -/
theorem degreeOneFirstLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    degreeOneFirstLocal δ j x y = degreeOneResidue hxy := sorry

/-- On an immediate specialization, the second degree-one local component is the divisor
order. -/
theorem degreeOneSecondLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    degreeOneSecondLocal δ j x y = degreeZeroResidue hxy := sorry

/-- The nonzero local residues of a fixed Milnor class have finite support. -/
theorem degreeOneFirstLocal_finiteSupport {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    (j : ℤ)
    (x : {x : X // δ x = j + 1})
    (a : Group 2 (X.residueField x.1)) :
    {y : {y : X // δ y = j} | degreeOneFirstLocal δ j x y a ≠ 0}.Finite := sorry

/-- The sum of local residues sends zero to zero. -/
private theorem degreeOneFirst_map_zero {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1}) :
    (∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y 0)) = 0 := sorry

/-- The sum of local residues preserves addition. -/
private theorem degreeOneFirst_map_add {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1})
    (a b : Group 2 (X.residueField x.1)) :
    (∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y (a + b))) =
      (∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y a)) +
        (∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y b)) := sorry

/-- The first degree-one coniveau arrow, assembled from local tame symbols. -/
@[no_expose] noncomputable def degreeOneFirst {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ) :
    Term X δ 2 (j + 1) →+ Term X δ 1 j :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y a)
        map_zero' := degreeOneFirst_map_zero δ j x
        map_add' := degreeOneFirst_map_add δ j x }

/-- The nonzero local residues of a fixed Milnor class have finite support. -/
theorem degreeOneSecondLocal_finiteSupport {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    (j : ℤ)
    (x : {x : X // δ x = j})
    (a : Group 1 (X.residueField x.1)) :
    {y : {y : X // δ y = j - 1} | degreeOneSecondLocal δ j x y a ≠ 0}.Finite := sorry

/-- The sum of local residues sends zero to zero. -/
private theorem degreeOneSecond_map_zero {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j}) :
    (∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y 0)) = 0 := sorry

/-- The sum of local residues preserves addition. -/
private theorem degreeOneSecond_map_add {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j})
    (a b : Group 1 (X.residueField x.1)) :
    (∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y (a + b))) =
      (∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y a)) +
        (∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y b)) := sorry

/-- The second degree-one coniveau arrow, assembled from local divisor orders. -/
@[no_expose] noncomputable def degreeOneSecond {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ) :
    Term X δ 1 j →+ Term X δ 0 (j - 1) :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y a)
        map_zero' := degreeOneSecond_map_zero δ j x
        map_add' := degreeOneSecond_map_add δ j x }

/-- Evaluating the first degree-one arrow on a homogeneous summand is the corresponding local
tame-symbol sum. -/
theorem degreeOneFirst_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1}) (a : Group 2 (X.residueField x.1)) :
    degreeOneFirst δ j (termOf x a) =
      ∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y a) := sorry

/-- Evaluating the second degree-one arrow on a homogeneous summand is the corresponding local
divisor-order sum. -/
theorem degreeOneSecond_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j}) (a : Group 1 (X.residueField x.1)) :
    degreeOneSecond δ j (termOf x a) =
      ∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y a) := sorry


/-- The coefficient of the assembled arrow on a summand is its local residue. -/
theorem excellentFirst_of_apply {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1})
    (a : Group (i + 1) (X.residueField x.1)) (y : {y : X // δ y = j}) :
    excellentFirst δ transfers i j (termOf x a) y = excellentFirstLocal δ transfers i j x y a := sorry


/-- The coefficient of the assembled arrow on a summand is its local residue. -/
theorem excellentSecond_of_apply {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j})
    (a : Group i (X.residueField x.1)) (y : {y : X // δ y = j - 1}) :
    excellentSecond δ transfers i hi j (termOf x a) y = excellentSecondLocal δ transfers i hi j x y a := sorry


/-- The coefficient of the assembled arrow on a summand is its local residue. -/
theorem degreeOneFirst_of_apply {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    (j : ℤ)
    (x : {x : X // δ x = j + 1})
    (a : Group 2 (X.residueField x.1)) (y : {y : X // δ y = j}) :
    degreeOneFirst δ j (termOf x a) y = degreeOneFirstLocal δ j x y a := sorry


/-- The coefficient of the assembled arrow on a summand is its local residue. -/
theorem degreeOneSecond_of_apply {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    (j : ℤ)
    (x : {x : X // δ x = j})
    (a : Group 1 (X.residueField x.1)) (y : {y : X // δ y = j - 1}) :
    degreeOneSecond δ j (termOf x a) y = degreeOneSecondLocal δ j x y a := sorry

/-- The fixed branchwise Milnor norm family for immediate specializations, independent
of the dimension function and the two coniveau degrees. -/
noncomputable def canonicalSpecializationTransfers
    (X : Scheme.{u}) [IsNoetherian X] [Scheme.Excellent X] :
    SpecializationTransfers X :=
  fun hxy b ↦ normalizationResidueMilnorNorm
    (SpecializationLocalRing hxy.specializes) (X.residueField _) b

/-- Each member of the fixed specialization family is the normalization-residue Milnor norm. -/
theorem canonicalSpecializationTransfers_apply
    (X : Scheme.{u}) [IsNoetherian X] [Scheme.Excellent X] {x y : X}
    (hxy : IsImmediateSpecialization x y)
    (b : NormalizationBranch (SpecializationLocalRing hxy.specializes) (X.residueField x)) :
    canonicalSpecializationTransfers X hxy b =
      normalizationResidueMilnorNorm (SpecializationLocalRing hxy.specializes)
        (X.residueField x) b := rfl

/-- The first coniveau arrow, assembled from
excellent local residues on immediate specializations. -/
noncomputable def canonicalExcellentFirst
    (X : Scheme.{u}) [IsNoetherian X] (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (i : ℕ) (j : ℤ) :
    MilnorK.Coniveau.Term X δ (i + 1) (j + 1) →+ MilnorK.Coniveau.Term X δ i j :=
  MilnorK.Coniveau.excellentFirst δ (MilnorK.Coniveau.canonicalSpecializationTransfers X) i j

/-- The second coniveau arrow, assembled from
excellent local residues on immediate specializations. -/
noncomputable def canonicalExcellentSecond
    (X : Scheme.{u}) [IsNoetherian X] (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (i : ℕ) (hi : 1 ≤ i) (j : ℤ) :
    MilnorK.Coniveau.Term X δ i j →+ MilnorK.Coniveau.Term X δ (i - 1) (j - 1) :=
  MilnorK.Coniveau.excellentSecond δ (MilnorK.Coniveau.canonicalSpecializationTransfers X) i hi j

/-- On an immediate specialization, the first excellent arrow uses the excellent local residue. -/
theorem canonicalExcellentFirst_of_isImmediate
    (X : Scheme.{u}) [IsNoetherian X] (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j})
    (hxy : IsImmediateSpecialization x.1 y.1)
    (a : MilnorK.Group (i + 1) (X.residueField x.1)) :
    canonicalExcellentFirst X δ i j (MilnorK.Coniveau.termOf x a) y =
      MilnorK.Coniveau.excellentResidue hxy (MilnorK.Coniveau.canonicalSpecializationTransfers X hxy) i a := sorry

/-- For an excellent Noetherian scheme, Kato--Milnor
reciprocity makes the composition of the two consecutive tame-symbol arrows zero. -/
theorem comp_eq_zero_of_excellent
    (X : Scheme.{u}) [IsNoetherian X] (δ : X → ℤ) [IsDimensionFunction δ]
    [Scheme.Excellent X]
    (i : ℕ) (hi : 1 ≤ i) (j : ℤ) :
    (canonicalExcellentSecond X δ i hi j).comp
      (canonicalExcellentFirst X δ i j) = 0 := sorry

/-- In Milnor degree one, the composition of the two consecutive arrows is zero for every Noetherian scheme and every `j`. -/
theorem degreeOne_comp_eq_zero
    (X : Scheme.{u}) [IsNoetherian X] (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ) :
    (MilnorK.Coniveau.degreeOneSecond δ j).comp (MilnorK.Coniveau.degreeOneFirst δ j) = 0 := sorry

end MilnorK.Coniveau
