module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Inertia
public import ReasLib.RingTheory.Invariant.FixedPoints.QuotientGroup
public import ReasLib.RingTheory.Invariant.FixedPoints.ResidueField
public import ReasLib.RingTheory.Invariant.ResidueField

@[expose] public section

/-!
# Decomposition quotients and residue fields of fixed subalgebras

For a prime `m` in a finite invariant extension, the decomposition group modulo inertia acts on
the inertia-fixed subalgebra.  This leaf identifies that quotient with the Galois group of the
residue extension between the decomposition- and inertia-fixed subalgebras.
@stack 0BU6
-/

open scoped Pointwise

universe u v w

namespace Ideal.ResidueField.Invariant.Decomposition

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
variable [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- The canonical fixed-subalgebra algebra for the inclusion from decomposition fixed points to
inertia fixed points. -/
@[reducible, stacks 0BU6 "decomposition-to-inertia fixed-subalgebra algebra"]
noncomputable def fixedAlgebra (m : Ideal B) :
    Algebra
      (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
      (FixedPoints.subalgebra A B (m.inertia G)) :=
  FixedPoints.subalgebraAlgebraOfLe (Ideal.inertia_le_stabilizer m)

/-- The canonical action of the decomposition quotient on the inertia-fixed subalgebra. -/
@[reducible, stacks 0BU6 "decomposition quotient action on inertia fixed points"]
noncomputable def action (m : Ideal B) :
    MulSemiringAction (m.decompositionQuotient G)
      (FixedPoints.subalgebra A B (m.inertia G)) :=
  FixedPoints.quotientAction (A := A) (Ideal.inertia_le_stabilizer m)

/-- The decomposition quotient is the Galois group of the extension between decomposition and
inertia fixed subalgebras. -/
@[stacks 0BU6 "Galois quotient between decomposition and inertia fixed points"]
theorem isGaloisGroup (m : Ideal B) :
    -- Local instance justification (defeq pin): the Galois structure must use the named
    -- fixed-subalgebra inclusion and quotient action for this branch.
    letI : Algebra
        (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      fixedAlgebra m
    letI : MulSemiringAction (m.decompositionQuotient G)
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      action m
    IsGaloisGroup (m.decompositionQuotient G)
      (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
      (FixedPoints.subalgebra A B (m.inertia G)) := sorry

-- Proof strategy: unfold `fixedAlgebra`, `action`, and `Ideal.decompositionQuotient`; this is
-- exactly `FixedPoints.quotientIsGaloisGroup (Ideal.inertia_le_stabilizer m)`, using normality of
-- inertia in the decomposition group.

/-- The contraction to the inertia-fixed subalgebra lies over the contraction to the
decomposition-fixed subalgebra. -/
@[stacks 0BU6 "inertia-fixed contraction over the decomposition-fixed contraction"]
theorem liesOver (m : Ideal B) :
    -- Local instance justification (defeq pin): `LiesOver` is relative to the canonical
    -- fixed-subalgebra algebra named by `fixedAlgebra m`.
    letI : Algebra
        (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      fixedAlgebra m
    (m.under (FixedPoints.subalgebra A B (m.inertia G))).LiesOver
      (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))) := sorry

-- Proof strategy: unfold `fixedAlgebra` and apply
-- `FixedPoints.under_liesOver_under_of_le (Ideal.inertia_le_stabilizer m) m`.

/-- Every element of the decomposition quotient fixes the contracted ideal in the inertia-fixed
subalgebra. -/
@[stacks 0BU6 "decomposition quotient fixes the inertia contraction"]
theorem smul_inertiaUnder (m : Ideal B) (sigma : m.decompositionQuotient G) :
    -- Local instance justification (defeq pin): the ideal action is the named quotient action
    -- on the inertia-fixed subalgebra.
    letI : MulSemiringAction (m.decompositionQuotient G)
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      action m
    sigma • (m.under (FixedPoints.subalgebra A B (m.inertia G))) =
      m.under (FixedPoints.subalgebra A B (m.inertia G)) := sorry

-- Proof strategy: unfold `action` and `Ideal.decompositionQuotient`, then specialize
-- `FixedPoints.quotientAction_smul_under_of_le_stabilizer` to the inertia/decomposition inclusion;
-- the decomposition group stabilizes `m` by definition.

/-- The decomposition quotient has trivial inertia at the contracted ideal of the inertia-fixed
subalgebra. -/
@[stacks 0BU6 "trivial inertia of the decomposition quotient"]
theorem inertia_eq_bot (m : Ideal B) :
    -- Local instance justification (defeq pin): inertia is computed for the named quotient
    -- action `action m`.
    letI : MulSemiringAction (m.decompositionQuotient G)
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      action m
    (m.under (FixedPoints.subalgebra A B (m.inertia G))).inertia
      (m.decompositionQuotient G) = ⊥ := sorry

-- Proof strategy: prove subgroup extensionality.  Lift a quotient element to the decomposition
-- group; membership in the displayed inertia says its action on the residue field is trivial.
-- Translate this with `Ideal.mem_inertia_iff` to membership of the representative in `m.inertia
-- G`, whose class in the decomposition quotient is one.  The reverse inclusion is immediate.

/-- The residue-field algebra induced by the decomposition/inertia lying-over pair. -/
@[reducible, stacks 0BU6 "decomposition-to-inertia residue-field algebra"]
noncomputable def residueAlgebra (m : Ideal B) [m.IsPrime] :
    Algebra
      (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField
      (m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField :=
  FixedPoints.ResidueField.algebraOfLe (Ideal.inertia_le_stabilizer m) m

/-- The canonical homomorphism from the decomposition quotient to the Galois group of the residue
extension between decomposition- and inertia-fixed contractions. -/
@[reducible, stacks 0BU6 "decomposition quotient action on the inertia residue field"]
noncomputable def residueHom (m : Ideal B) [m.IsPrime] :
    -- Local instance justification (defeq pin): all structures below are the named fixed-point
    -- and residue-field owners for this lying-over pair.
    letI : Algebra
        (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      fixedAlgebra m
    letI : MulSemiringAction (m.decompositionQuotient G)
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      action m
    letI : IsGaloisGroup (m.decompositionQuotient G)
        (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      isGaloisGroup m
    letI : (m.under (FixedPoints.subalgebra A B (m.inertia G))).LiesOver
        (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))) :=
      liesOver m
    letI : Algebra
        (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField
        (m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField :=
      residueAlgebra m
    m.decompositionQuotient G →*
      Gal((m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField /
        (m.under
          (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField) :=
  letI : Algebra
      (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
      (FixedPoints.subalgebra A B (m.inertia G)) :=
    fixedAlgebra m
  letI : MulSemiringAction (m.decompositionQuotient G)
      (FixedPoints.subalgebra A B (m.inertia G)) :=
    action m
  letI : IsGaloisGroup (m.decompositionQuotient G)
      (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
      (FixedPoints.subalgebra A B (m.inertia G)) :=
    isGaloisGroup m
  letI : (m.under (FixedPoints.subalgebra A B (m.inertia G))).LiesOver
      (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))) :=
    liesOver m
  letI : Algebra
      (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField
      (m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField :=
    residueAlgebra m
  Ideal.ResidueField.Invariant.homOfFixed (m.decompositionQuotient G)
    (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m)))
    (m.under (FixedPoints.subalgebra A B (m.inertia G)))
    (smul_inertiaUnder m)

/-- The decomposition quotient acts bijectively on the residue-field Galois group between the
decomposition- and inertia-fixed contractions. -/
@[stacks 0BU6 "decomposition quotient is the fixed-point residue Galois group"]
theorem residueHom_bijective (m : Ideal B) [m.IsPrime] :
    -- Local instance justification (defeq pin): bijectivity is for the canonical action,
    -- contraction, and residue algebra selected by the named owners above.
    letI : Algebra
        (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      fixedAlgebra m
    letI : MulSemiringAction (m.decompositionQuotient G)
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      action m
    letI : IsGaloisGroup (m.decompositionQuotient G)
        (FixedPoints.subalgebra A B (MulAction.stabilizer G m))
        (FixedPoints.subalgebra A B (m.inertia G)) :=
      isGaloisGroup m
    letI : (m.under (FixedPoints.subalgebra A B (m.inertia G))).LiesOver
        (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))) :=
      liesOver m
    letI : Algebra
        (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField
        (m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField :=
      residueAlgebra m
    Function.Bijective (residueHom (A := A) (B := B) (G := G) m) := sorry

-- Proof strategy: unfold `residueHom` and apply
-- `Ideal.ResidueField.Invariant.homOfFixed_bijective`.  Supply `smul_inertiaUnder m` for global
-- stability and `inertia_eq_bot m` for the trivial-inertia hypothesis; `isGaloisGroup m` supplies
-- the invariant extension.

/-- The residue extension between the decomposition- and inertia-fixed contractions is Galois. -/
@[stacks 0BU6 "Galois residue extension between decomposition and inertia fixed points"]
theorem isGalois (m : Ideal B) [m.IsPrime] :
    -- Local instance justification (defeq pin): the residue extension is measured using the
    -- named residue-field algebra, not an arbitrary inferred structure.
    letI : Algebra
        (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField
        (m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField :=
      residueAlgebra m
    IsGalois
      (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField
      (m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField := sorry

-- Proof strategy: install the named action, fixed-subalgebra Galois structure, lying-over pair,
-- and residue algebra.  Use the finite decomposition quotient together with
-- `residueHom_bijective` to obtain the canonical residue-field `IsGaloisGroup`, then apply
-- `IsGaloisGroup.isGalois`.

/-- The residue-field Galois group and the decomposition quotient have equal cardinality. -/
@[stacks 0BU6 "cardinality of the decomposition residue Galois group"]
theorem natCard_gal_eq_decompositionQuotient (m : Ideal B) [m.IsPrime] :
    -- Local instance justification (defeq pin): the Galois-group carrier uses the named residue
    -- algebra attached to this contraction pair.
    letI : Algebra
        (m.under (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField
        (m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField :=
      residueAlgebra m
    Nat.card
        (Gal((m.under (FixedPoints.subalgebra A B (m.inertia G))).ResidueField /
          (m.under
            (FixedPoints.subalgebra A B (MulAction.stabilizer G m))).ResidueField)) =
      Nat.card (m.decompositionQuotient G) := sorry

-- Proof strategy: apply `Nat.card_congr` to the equivalence obtained from
-- `Equiv.ofBijective (residueHom m) (residueHom_bijective m)` and reverse the resulting equality.

end Ideal.ResidueField.Invariant.Decomposition
