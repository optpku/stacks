module

public import ReasLib.FieldTheory.Galois.FixedField
public import ReasLib.FieldTheory.Galois.IntegralClosure.Etale
public import ReasLib.FieldTheory.Galois.IntegralClosure.FixedPoints.Ramification
public import ReasLib.RingTheory.Invariant.FixedPoints.Prime
public import ReasLib.RingTheory.Invariant.ResidueField.Decomposition
import StacksCheckRecall

@[expose] public section

/-!
# The ramification tower at a maximal ideal

@stack 0BU6

`Remark 15.113.9` records the fixed fields, fixed subalgebras, contracted ideals, and residue
fields associated to the tower `P ≤ I ≤ D` of wild inertia, inertia, and decomposition groups.
-/

open scoped Pointwise
open Ideal IsLocalRing Algebra IntermediateField
open integralClosure.FixedPoints.Ramification.Wild

universe u v w

noncomputable section

section

namespace Remark_15_113_9

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "κA" => Ideal.ResidueField p

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

-- Source compatibility note: the displayed Stacks diagram uses the
-- conventional names `P`, `I`, `D`, and their fixed objects; the underlying reusable API remains
-- `Ideal`, `FixedPoints`, `IntermediateField`, and `Ideal.under`.
/- The following notation is source-facing only: it records the displayed tower `P ≤ I ≤ D` and
its fixed objects.  The underlying groups, subalgebras, fields, and contractions remain canonical
`Ideal`, `FixedPoints`, `IntermediateField`, and `Ideal.under` objects. -/
local notation "D" => MulAction.stabilizer G m
local notation "I" => m.inertia G
local notation "P" => m.wildInertia G
local notation "I_t" => m.tameInertia G

local notation "B[D]" => FixedPoints.subalgebra A B D
local notation "B[I]" => FixedPoints.subalgebra A B I
local notation "B[P]" => FixedPoints.subalgebra A B P

local notation "L[D]" => IntermediateField.fixedField D
local notation "L[I]" => IntermediateField.fixedField I
local notation "L[P]" => IntermediateField.fixedField P

local notation "mD" => m.under B[D]
local notation "mI" => m.under B[I]
local notation "mP" => m.under B[P]

local notation "κD" => Ideal.ResidueField mD
local notation "κI" => Ideal.ResidueField mI
local notation "κP" => Ideal.ResidueField mP

/- The contraction statements are recalled through the canonical `LiesOver` API.  This keeps the
source-facing tower readable while making the reusable owner independent of this chapter. -/
/- Remark 15.113.9 (setup): the decomposition contraction lies over the base branch. -/
@[stacks 0BU6 "decomposition contraction over base"]
#check (integralClosure.FixedPoints.ResidueField.under_liesOver_maximalIdeal
  (A := A) (K := K) (L := L) D m : Ideal.LiesOver mD p)

/- Remark 15.113.9 (setup): the wild-inertia contraction lies over the base branch. -/
@[stacks 0BU6 "wild contraction over base"]
#check (integralClosure.FixedPoints.ResidueField.under_liesOver_maximalIdeal
  (A := A) (K := K) (L := L) P m : Ideal.LiesOver mP p)

/- Remark 15.113.9 (1): the fixed-field extension `L^I / L^D` is Galois. -/
@[stacks 0BU6 "Remark 15.113.9 (1): inertia over decomposition fixed field"]
#check (IntermediateField.fixedField_isGalois_of_normal (F := K) (E := L)
  (Ideal.inertia_le_stabilizer m) :
    letI : Algebra (L[D]) (L[I]) :=
      IntermediateField.fixedFieldAlgebraOfLe (Ideal.inertia_le_stabilizer m)
    IsGalois L[D] L[I])

/- Remark 15.113.9 (1): restriction identifies `D / I` with `Gal(L^I / L^D)`. -/
@[stacks 0BU6 "Remark 15.113.9 (1): inertia/decomposition fixed-field Galois group"]
#check (IntermediateField.fixedFieldQuotientHom_bijective (F := K) (E := L)
  (Ideal.inertia_le_stabilizer m) :
    letI : Algebra (L[D]) (L[I]) :=
      IntermediateField.fixedFieldAlgebraOfLe (Ideal.inertia_le_stabilizer m)
    Function.Bijective
      (IntermediateField.fixedFieldQuotientHom (F := K) (E := L)
        (Ideal.inertia_le_stabilizer m)))

/- Remark 15.113.9 (2): the fixed-field extension `L^P / L^I` is Galois. -/
@[stacks 0BU6 "Remark 15.113.9 (2): wild over inertia fixed field"]
#check (IntermediateField.fixedField_isGalois_of_normal (F := K) (E := L)
  (Ideal.wildInertia_le_inertia m) :
    letI : Algebra (L[I]) (L[P]) :=
      IntermediateField.fixedFieldAlgebraOfLe (Ideal.wildInertia_le_inertia m)
    IsGalois L[I] L[P])

/- Remark 15.113.9 (2): restriction identifies `I / P = I_t` with `Gal(L^P / L^I)`. -/
@[stacks 0BU6 "Remark 15.113.9 (2): tame quotient fixed-field Galois group"]
#check (IntermediateField.fixedFieldQuotientHom_bijective (F := K) (E := L)
  (Ideal.wildInertia_le_inertia m) :
    letI : Algebra (L[I]) (L[P]) :=
      IntermediateField.fixedFieldAlgebraOfLe (Ideal.wildInertia_le_inertia m)
    Function.Bijective
      (IntermediateField.fixedFieldQuotientHom (F := K) (E := L)
        (Ideal.wildInertia_le_inertia m)))

/- Remark 15.113.9 (3): the fixed-field extension `L^P / L^D` is Galois. -/
@[stacks 0BU6 "Remark 15.113.9 (3): wild over decomposition fixed field"]
#check (IntermediateField.fixedField_isGalois_of_normal (F := K) (E := L)
  (Ideal.wildInertia_le_stabilizer m) :
    letI : Algebra (L[D]) (L[P]) :=
      IntermediateField.fixedFieldAlgebraOfLe (Ideal.wildInertia_le_stabilizer m)
    IsGalois L[D] L[P])

/- Remark 15.113.9 (3): restriction identifies `D / P` with `Gal(L^P / L^D)`. -/
@[stacks 0BU6 "Remark 15.113.9 (3): wild/decomposition fixed-field Galois group"]
#check (IntermediateField.fixedFieldQuotientHom_bijective (F := K) (E := L)
  (Ideal.wildInertia_le_stabilizer m) :
    letI : Algebra (L[D]) (L[P]) :=
      IntermediateField.fixedFieldAlgebraOfLe (Ideal.wildInertia_le_stabilizer m)
    Function.Bijective
      (IntermediateField.fixedFieldQuotientHom (F := K) (E := L)
        (Ideal.wildInertia_le_stabilizer m)))

/- Remark 15.113.9 (4): `m^I` is the unique prime of `B^I` above `m^D`. -/
@[stacks 0BU6 "Remark 15.113.9 (4): inertia contraction uniqueness"]
#check (FixedPoints.primesOver_under_eq_singleton_of_le (A := A)
  (Ideal.inertia_le_stabilizer m) m
  (le_rfl : D ≤ MulAction.stabilizer G m) :
    letI : Algebra (B[D]) (B[I]) :=
      FixedPoints.subalgebraAlgebraOfLe (Ideal.inertia_le_stabilizer m)
    Ideal.primesOver mD (B[I]) = {mI})

/- Remark 15.113.9 (5): `m^P` is the unique prime of `B^P` above `m^I`. -/
@[stacks 0BU6 "Remark 15.113.9 (5): wild contraction uniqueness over inertia"]
#check (FixedPoints.primesOver_under_eq_singleton_of_le (A := A)
  (Ideal.wildInertia_le_inertia m) m (Ideal.inertia_le_stabilizer m) :
    letI : Algebra (B[I]) (B[P]) :=
      FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_inertia m)
    Ideal.primesOver mI (B[P]) = {mP})

/- Remark 15.113.9 (6): `m` is the unique prime of `B` lying over `m^P`. -/
@[stacks 0BU6 "Remark 15.113.9 (6): maximal branch over wild contraction"]
#check (FixedPoints.primesOver_under_eq_singleton (A := A) P m
  (Ideal.wildInertia_le_stabilizer m) : Ideal.primesOver mP B = {m})

/- Remark 15.113.9 (7): `m^P` is the unique prime of `B^P` above `m^D`. -/
@[stacks 0BU6 "Remark 15.113.9 (7): wild contraction uniqueness over decomposition"]
#check (FixedPoints.primesOver_under_eq_singleton_of_le (A := A)
  (Ideal.wildInertia_le_stabilizer m) m
  (le_rfl : D ≤ MulAction.stabilizer G m) :
    letI : Algebra (B[D]) (B[P]) :=
      FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_stabilizer m)
    Ideal.primesOver mD (B[P]) = {mP})

/- Remark 15.113.9 (8): `m` is the unique prime of `B` lying over `m^I`. -/
@[stacks 0BU6 "Remark 15.113.9 (8): maximal branch over inertia contraction"]
#check (FixedPoints.primesOver_under_eq_singleton (A := A) I m
  (Ideal.inertia_le_stabilizer m) : Ideal.primesOver mI B = {m})

/- Remark 15.113.9 (9): `m` is the unique prime of `B` lying over `m^D`. -/
@[stacks 0BU6 "Remark 15.113.9 (9): maximal branch over decomposition contraction"]
#check (FixedPoints.primesOver_under_eq_singleton (A := A) D m
  (le_rfl : D ≤ MulAction.stabilizer G m) : Ideal.primesOver mD B = {m})

/- Remark 15.113.9 (10): `A → B^D` is etale at `m^D`. -/
@[stacks 0BU6 "Remark 15.113.9 (10): decomposition fixed subalgebra etale"]
#check (integralClosure.FixedPoints.etaleAt_of_inertia_le
  (A := A) (K := K) (L := L) m D (Ideal.inertia_le_stabilizer m) :
  Algebra.IsEtaleAt A mD)

/- Remark 15.113.9 (10): the base/decomposition residue-field map is bijective. -/
@[stacks 0BU6 "Remark 15.113.9 (10): base/decomposition residue bijection"]
#check (integralClosure.FixedPoints.ResidueField.baseMap_bijective
  (A := A) (K := K) (L := L) m :
    letI : Algebra κA κD :=
      integralClosure.FixedPoints.ResidueField.algebraOfBase D m
    Function.Bijective (algebraMap κA κD))

/- Remark 15.113.9 (11): `B^D → B^I` is etale at `m^I`. -/
@[stacks 0BU6 "Remark 15.113.9 (11): decomposition/inertia etale"]
#check (integralClosure.FixedPoints.etaleAt_of_inertia_le_of_le
  (A := A) (K := K) (L := L) m (Ideal.inertia_le_stabilizer m)
  (le_rfl : I ≤ I) :
    letI : Algebra (B[D]) (B[I]) :=
      FixedPoints.subalgebraAlgebraOfLe (Ideal.inertia_le_stabilizer m)
    Algebra.IsEtaleAt (B[D]) mI)

/- Remark 15.113.9 (11): the residue-field extension `κ(m^I) / κ(m^D)` is Galois. -/
@[stacks 0BU6 "Remark 15.113.9 (11): decomposition/inertia residue Galois"]
#check (Ideal.ResidueField.Invariant.Decomposition.isGalois (A := A) m :
  letI : Algebra κD κI :=
    Ideal.ResidueField.Invariant.Decomposition.residueAlgebra (A := A) m
  IsGalois κD κI)

/- Remark 15.113.9 (11): the residue-field Galois group is `D / I`. -/
@[stacks 0BU6 "Remark 15.113.9 (11): decomposition/inertia residue Galois group"]
#check (Ideal.ResidueField.Invariant.Decomposition.residueHom_bijective
  (A := A) m :
    Function.Bijective
      (Ideal.ResidueField.Invariant.Decomposition.residueHom (A := A) m))

/- Remark 15.113.9 (12): `A → B^I` is etale at `m^I`. -/
@[stacks 0BU6 "Remark 15.113.9 (12): inertia fixed subalgebra etale"]
#check (integralClosure.FixedPoints.etaleAt_inertia (A := A) (K := K) (L := L) m :
  Algebra.IsEtaleAt A mI)

/- Remark 15.113.9 (13): the ramification index of `B^I ⊂ B^P` is `|I_t|`. -/
@[stacks 0BU6 "Remark 15.113.9 (13): inertia/wild ramification index"]
#check (ramificationIdx_eq_tameCard
  (A := A) (K := K) (L := L) m
  (le_rfl : I ≤ I)
  (Ideal.inertia_le_stabilizer m : I ≤ D) :
    letI : Algebra (B[I]) (B[P]) :=
      FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_inertia m)
    @Ideal.ramificationIdx (B[P]) _ mP (B[I]) _
      (FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_inertia m)) = Nat.card I_t)

/- Remark 15.113.9 (13): the residue-field map `κ(m^I) → κ(m^P)` is bijective. -/
@[stacks 0BU6 "Remark 15.113.9 (13): inertia/wild residue bijection"]
#check (residueMap_bijective
  (A := A) (K := K) (L := L) m
  (Ideal.wildInertia_le_inertia m : P ≤ I) (le_rfl : I ≤ I) :
    letI : Algebra κI κP :=
      FixedPoints.ResidueField.algebraOfLe (A := A) (H := P) (H' := I)
        (Ideal.wildInertia_le_inertia m : P ≤ I) m
    Function.Bijective (algebraMap κI κP))

/- Remark 15.113.9 (13): the tame ramification index is prime to the residue characteristic. -/
@[stacks 0BU6 "Remark 15.113.9 (13): inertia/wild tame coprimality"]
#check (ramificationIdx_coprime_of_charP
  (A := A) (K := K) (L := L) m
  (Ideal.wildInertia_le_inertia m : P ≤ I)
  (Ideal.inertia_le_stabilizer m : I ≤ D) :
    ∀ (q : ℕ) [Fact q.Prime] [CharP κI q],
      Nat.Coprime
        (@Ideal.ramificationIdx (B[P]) _ mP (B[I]) _
          (FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_inertia m))) q)

/- Remark 15.113.9 (14): the ramification index of `B^D ⊂ B^P` is `|I_t|`. -/
@[stacks 0BU6 "Remark 15.113.9 (14): decomposition/wild ramification index"]
#check (ramificationIdx_eq_tameCard
  (A := A) (K := K) (L := L) m
  (Ideal.inertia_le_stabilizer m : I ≤ D) (le_rfl : D ≤ D) :
    letI : Algebra (B[D]) (B[P]) :=
      FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_stabilizer m)
    @Ideal.ramificationIdx (B[P]) _ mP (B[D]) _
      (FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_stabilizer m)) = Nat.card I_t)

/- Remark 15.113.9 (14): the residue-field extension `κ(m^P) / κ(m^D)` is separable. -/
@[stacks 0BU6 "Remark 15.113.9 (14): decomposition/wild residue separability"]
#check (residue_isSeparable
  (A := A) (K := K) (L := L) m
  (Ideal.wildInertia_le_stabilizer m : P ≤ D) (le_rfl : D ≤ D) :
    letI : Algebra κD κP :=
      FixedPoints.ResidueField.algebraOfLe (A := A) (H := P) (H' := D)
        (Ideal.wildInertia_le_stabilizer m : P ≤ D) m
    Algebra.IsSeparable κD κP)

/- Remark 15.113.9 (14): the tame ramification index is prime to the residue characteristic. -/
@[stacks 0BU6 "Remark 15.113.9 (14): decomposition/wild tame coprimality"]
#check (ramificationIdx_coprime_of_charP
  (A := A) (K := K) (L := L) m
  (Ideal.wildInertia_le_stabilizer m : P ≤ D) (le_rfl : D ≤ D) :
    ∀ (q : ℕ) [Fact q.Prime] [CharP κD q],
      Nat.Coprime
        (@Ideal.ramificationIdx (B[P]) _ mP (B[D]) _
          (FixedPoints.subalgebraAlgebraOfLe (Ideal.wildInertia_le_stabilizer m))) q)

/- Remark 15.113.9 (15): the ramification index of `A ⊂ B^P` is `|I_t|`. -/
@[stacks 0BU6 "Remark 15.113.9 (15): base/wild ramification index"]
#check (base_ramificationIdx_eq_tameCard
  (A := A) (K := K) (L := L) m :
    @Ideal.ramificationIdx (B[P]) _ mP A _
      (inferInstance : Algebra A (B[P])) = Nat.card I_t)

/- Remark 15.113.9 (15): the residue-field extension `κ(m^P) / κ(A)` is separable. -/
@[stacks 0BU6 "Remark 15.113.9 (15): base/wild residue separability"]
#check (base_residue_isSeparable
  (A := A) (K := K) (L := L) m :
    letI : Algebra κA κP :=
      integralClosure.FixedPoints.ResidueField.algebraOfBase P m
    Algebra.IsSeparable κA κP)

/- Remark 15.113.9 (15): the tame ramification index is prime to the residue characteristic. -/
@[stacks 0BU6 "Remark 15.113.9 (15): base/wild tame coprimality"]
#check (base_ramificationIdx_coprime_of_charP
  (A := A) (K := K) (L := L) m :
    ∀ (q : ℕ) [Fact q.Prime] [CharP κA q],
      Nat.Coprime
        (@Ideal.ramificationIdx (B[P]) _ mP A _
          (inferInstance : Algebra A (B[P]))) q)

end Remark_15_113_9

end
