module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction

/-!
# Integer translation on the affine line

The additive integers act on the affine line by translations, inducing automorphisms of
its generic residue field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- The acting group, represented as a universe-small multiplicative lift of the integers. -/
abbrev group : Type u := Multiplicative (ULift.{u} ℤ)

/-- Recover an ordinary integer from an element of the acting group. -/
def toInt (n : group) : ℤ := n.toAdd.down

/-- The inclusion of ordinary integers into the acting group. -/
def ofInt (n : ℤ) : group := Multiplicative.ofAdd (ULift.up n)

/-- The two explicit presentations of an integer agree. -/
theorem toInt_ofInt (n : ℤ) : toInt (ofInt n) = n := by rfl

/-- The inclusion of an integer recovers the original acting-group element. -/
theorem ofInt_toInt (n : group) : ofInt (toInt n) = n := by
  cases n
  rfl

/-- The zero integer represents the identity of the acting group. -/
theorem ofInt_zero : ofInt 0 = 1 := by rfl

/-- The canonical affine line over a characteristic-zero field is integral. -/
instance instIsIntegral_cover (k : Type u) [Field k] [CharZero k] :
    IsIntegral (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left :=
  inferInstanceAs (IsIntegral (𝔸(ULift.{u} (Fin 1); AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k)))

/-- Translation by an integer, viewed as an automorphism of the canonical affine line. -/
def translateAut (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    Aut (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k) where
  hom := AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k n
  inv := AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k (-n)
  hom_inv_id := AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate_neg k n
  inv_hom_id := by simpa using AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate_neg k (-n)

/-- The forward map of the translation automorphism. -/
theorem translateAut_hom (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    (translateAut k n).hom = AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k n := by rfl

/-- The inverse map of the translation automorphism. -/
theorem translateAut_inv (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    (translateAut k n).inv = AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k (-n) := by rfl

/-- The translation action of the lifted integers on the affine line. -/
def action (k : Type u) [Field k] [CharZero k] : group →* Aut (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k) where
  toFun n := translateAut k (toInt n)
  map_one' := by
    apply CategoryTheory.Aut.ext
    change AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k 0 = 𝟙 _
    exact AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate_zero k
  map_mul' := by
    intro m n
    have hmn : toInt (m * n) = toInt m + toInt n := by rfl
    apply CategoryTheory.Aut.ext
    change AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k (toInt (m * n)) = _
    rw [hmn, CategoryTheory.Aut.Aut_mul_def]
    change AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k (toInt m + toInt n) =
      AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k (toInt n) ≫
        AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate k (toInt m)
    rw [← AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.translate_add k (toInt n) (toInt m)]
    simp [add_comm]

/-- Evaluation of the translation action at a group element. -/
theorem action_apply (k : Type u) [Field k] [CharZero k] (n : group) :
    action k n = translateAut k (toInt n) := by rfl

/-- Evaluation of the action on an ordinary integer. -/
theorem action_ofInt (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    action k (ofInt n) = translateAut k n := by simp [action, toInt_ofInt]

/-- Every translation fixes the generic point of the affine line. -/
theorem action_genericPoint (k : Type u) [Field k] [CharZero k] (n : group) :
    (action k n).hom.left (genericPoint (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left) =
      genericPoint (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left := by sorry

/-- A nonidentity translation fixes precisely the generic point. -/
theorem fixed_iff_genericPoint (k : Type u) [Field k] [CharZero k] {n : group}
    (hn : n ≠ 1) (u : (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left) :
    (action k n).hom.left u = u ↔
      u = genericPoint (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left := by sorry

/-- The automorphism induced on the residue field by a translation. -/
def genericResidueAut (k : Type u) [Field k] [CharZero k] (n : group) :
    (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left.residueField
        (genericPoint (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left) ⟶
      (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left.residueField
        (genericPoint (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left) :=
  residueFieldAut (action k) n (action_genericPoint k n)

/-- Every induced generic residue-field map is an isomorphism. -/
instance instIsIso_genericResidueAut (k : Type u) [Field k] [CharZero k] (n : group) :
    IsIso (genericResidueAut k n) := by sorry

/-- Distinct integers induce distinct automorphisms of the generic residue field. -/
theorem injective_genericResidueAut (k : Type u) [Field k] [CharZero k] :
    Function.Injective (genericResidueAut k) := by sorry

/-- The translation action is free on residue fields. -/
instance instIsResidueFieldFree_action (k : Type u) [Field k] [CharZero k] :
    IsResidueFieldFree (action k) := by sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
