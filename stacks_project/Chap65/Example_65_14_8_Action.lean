module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import stacks_project.Chap65.Lemma_65_14_3_Relation

/-!
# Integer translation action on the affine line

This module records the affine line `U = 𝔸¹_k` over a characteristic-zero field and the
left translation action of `ℤ` by `n(x) = x + n`, packaged as a homomorphism into `Aut U`
for `Scheme.PreRelation.ofAut`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AffineSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- The acting group `ℤ`, as a `Type u` multiplicative group. -/
abbrev group : Type u := Multiplicative (ULift.{u} ℤ)

/-- The acting group is `Multiplicative` of a `u`-lift of `ℤ`. -/
theorem group_eq : group = Multiplicative (ULift.{u} ℤ) := sorry

/-- The acting group is `u`-small, so the coproduct `∐_G U` exists in `Over (Spec k)`. -/
instance instSmall_group : Small.{u, u} group := inferInstance

/-- Recover the underlying integer of a group element. -/
def toInt (n : group) : ℤ := n.toAdd.down

/-- `toInt` is the down-projection of the additive `ULift`. -/
theorem toInt_eq (n : group) : toInt n = n.toAdd.down := sorry

/-- The group element associated to an integer. -/
def ofInt (n : ℤ) : group := Multiplicative.ofAdd (ULift.up n)

/-- `ofInt` is `Multiplicative.ofAdd` of a `ULift`. -/
theorem ofInt_eq (n : ℤ) : ofInt n = Multiplicative.ofAdd (ULift.up n) := sorry

/-- `toInt` inverts `ofInt`. -/
theorem toInt_ofInt (n : ℤ) : toInt (ofInt n) = n := sorry

/-- `ofInt` inverts `toInt`. -/
theorem ofInt_toInt (n : group) : ofInt (toInt n) = n := sorry

/-- The identity of `group` is translation by `0`. -/
theorem ofInt_zero : ofInt 0 = 1 := sorry

/-- The base scheme `S = Spec k`. -/
abbrev base (k : Type u) [Field k] [CharZero k] : Scheme.{u} :=
  Spec (CommRingCat.of.{u} k)

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] [CharZero k] :
    base k = Spec (CommRingCat.of.{u} k) := sorry

/-- The spectrum of a characteristic-zero field is integral. -/
instance instIsIntegral_base (k : Type u) [Field k] [CharZero k] : IsIntegral (base k) :=
  inferInstance

/-- The affine line `U = 𝔸¹_k` as a scheme over `Spec k`. -/
def cover (k : Type u) [Field k] [CharZero k] : Over (base k) :=
  asOver (𝔸(ULift.{u} (Fin 1); base k)) (base k)

/-- The underlying scheme of the cover is the relative affine line. -/
theorem cover_left (k : Type u) [Field k] [CharZero k] :
    (cover k).left = 𝔸(ULift.{u} (Fin 1); base k) := sorry

/-- The structure morphism of the cover is the canonical projection of affine space. -/
theorem cover_hom (k : Type u) [Field k] [CharZero k] :
    (cover k).hom = 𝔸(ULift.{u} (Fin 1); base k) ↘ base k := sorry

/-- Affine 1-space over a field is integral. -/
instance instIsIntegral_cover (k : Type u) [Field k] [CharZero k] :
    IsIntegral (cover k).left :=
  inferInstanceAs (IsIntegral (𝔸(ULift.{u} (Fin 1); base k)))

/-- The standard coordinates of `𝔸¹_k`. -/
def coord (k : Type u) [Field k] [CharZero k] (i : ULift.{u} (Fin 1)) :
    Γ((cover k).left, ⊤) :=
  AffineSpace.coord (base k) i

/-- `coord k i` is the standard coordinate of the relative affine line. -/
theorem coord_eq (k : Type u) [Field k] [CharZero k] (i : ULift.{u} (Fin 1)) :
    coord k i = AffineSpace.coord (base k) i := sorry

/-- Translation by `n` on the underlying affine line, sending a point `x` to `x + n`. -/
def translateLeft (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    (cover k).left ⟶ (cover k).left :=
  homOfVector (cover k).hom fun i : ULift.{u} (Fin 1) ↦
    coord k i + (n : Γ((cover k).left, ⊤))

/-- `translateLeft k n` is `homOfVector` of the translated coordinates. -/
theorem translateLeft_eq (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    translateLeft k n =
      homOfVector (cover k).hom fun i : ULift.{u} (Fin 1) ↦
        coord k i + (n : Γ((cover k).left, ⊤)) := sorry

/-- Translation by `n` commutes with the structure morphism of the affine line. -/
theorem translate_w (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    translateLeft k n ≫ (cover k).hom = (cover k).hom := sorry

/-- Translation by `n` as a morphism of the affine line over `Spec k`. -/
def translate (k : Type u) [Field k] [CharZero k] (n : ℤ) : cover k ⟶ cover k :=
  Over.homMk (translateLeft k n) (translate_w k n)

/-- The underlying scheme morphism of `translate k n` is `translateLeft k n`. -/
theorem translate_left (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    (translate k n).left = translateLeft k n := sorry

/-- Translation by zero is the identity. -/
theorem translate_zero (k : Type u) [Field k] [CharZero k] :
    translate k 0 = 𝟙 (cover k) := sorry

/-- Translation is a homomorphism from `(ℤ, +)` to endomorphisms of the cover. -/
theorem translate_add (k : Type u) [Field k] [CharZero k] (m n : ℤ) :
    translate k (m + n) = translate k m ≫ translate k n := sorry

/-- Translation by `n` is inverted by translation by `-n`. -/
theorem translate_neg (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    translate k n ≫ translate k (-n) = 𝟙 (cover k) := sorry

/-- Translation by `-n` is inverted by translation by `n`. -/
theorem translate_neg' (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    translate k (-n) ≫ translate k n = 𝟙 (cover k) := sorry

/-- Translation by `n` as an automorphism of the affine line over `Spec k`. -/
def translateAut (k : Type u) [Field k] [CharZero k] (n : ℤ) : Aut (cover k) where
  hom := translate k n
  inv := translate k (-n)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `translateAut k n` is translation by `n`. -/
theorem translateAut_hom (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    (translateAut k n).hom = translate k n := sorry

/-- The inverse map of `translateAut k n` is translation by `-n`. -/
theorem translateAut_inv (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    (translateAut k n).inv = translate k (-n) := sorry

/-- The left translation action of `ℤ` on `U = 𝔸¹_k`. -/
def action (k : Type u) [Field k] [CharZero k] : group →* Aut (cover k) where
  toFun n := translateAut k (toInt n)
  map_one' := sorry
  map_mul' := sorry

/-- The action of `n` is translation by `toInt n`. -/
theorem action_apply (k : Type u) [Field k] [CharZero k] (n : group) :
    action k n = translateAut k (toInt n) := sorry

/-- The action of an integer is translation by that integer. -/
theorem action_ofInt (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    action k (ofInt n) = translateAut k n := sorry

/-- The defining arrow of `ofAut (action k)` is the coproduct of graphs `(n·x, x)`. -/
theorem ofAut_action_hom (k : Type u) [Field k] [CharZero k] :
    (ofAut (action k)).hom = relationHom (action k) := sorry

/-- Translation by a group element fixes the generic point of the affine line. -/
theorem action_genericPoint (k : Type u) [Field k] [CharZero k] (n : group) :
    (action k n).hom.left (genericPoint (cover k).left) =
      genericPoint (cover k).left := sorry

/-- A non-identity translation of the affine line over a characteristic-zero field
fixes a point if and only if that point is the generic point. -/
theorem fixed_iff_genericPoint (k : Type u) [Field k] [CharZero k] {n : group}
    (hn : n ≠ 1) (u : (cover k).left) :
    (action k n).hom.left u = u ↔ u = genericPoint (cover k).left := sorry

/-- The residue-field automorphism of `k(x)` induced by translation by `n`. -/
def genericResidueAut (k : Type u) [Field k] [CharZero k] (n : group) :
    (cover k).left.residueField (genericPoint (cover k).left) ⟶
      (cover k).left.residueField (genericPoint (cover k).left) :=
  residueFieldAut (action k) n (action_genericPoint k n)

/-- `genericResidueAut` is `residueFieldAut` at the generic point. -/
theorem genericResidueAut_eq (k : Type u) [Field k] [CharZero k] (n : group) :
    genericResidueAut k n =
      residueFieldAut (action k) n (action_genericPoint k n) := sorry

/-- Each translation induces an automorphism of the residue field `k(x)`. -/
instance instIsIso_genericResidueAut (k : Type u) [Field k] [CharZero k] (n : group) :
    IsIso (genericResidueAut k n) := sorry

/-- Characteristic zero makes `ℤ` inject into the automorphism group of `k(x)`. -/
theorem injective_genericResidueAut (k : Type u) [Field k] [CharZero k] :
    Function.Injective (genericResidueAut k) := sorry

/-- Integer translation on the affine line over a characteristic-zero field is residue-field
free in the sense of hypothesis (*) of Lemma 65.14.3. -/
instance instIsResidueFieldFree_action (k : Type u) [Field k] [CharZero k] :
    IsResidueFieldFree (action k) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
