/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Instances

/-!
# Inverse limits of sequences in `ArtinianLocalAlgCat`

The inverse limit of a sequence `A (n + 1) ⟶ A n` in `C_Λ` is the ring of
compatible families in the product of the carriers, with canonical projections
and kernels.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable (A : ℕ → ArtinianLocalAlgCat Λ k) (f : ∀ n, A (n + 1) ⟶ A n)

/-- Inverse limit of a sequence in `ArtinianLocalAlgCat`, as compatible families. -/
def inverseLimit : Type u :=
  { x : ∀ n, (A n).carrier // ∀ n, (f n).hom (x (n + 1)) = x n }

/-- Pointwise zero of a compatible family. -/
instance instZero_inverseLimit : Zero (inverseLimit A f) where
  zero := ⟨0, fun n ↦ map_zero (f n).hom⟩

/-- Pointwise one of a compatible family. -/
instance instOne_inverseLimit : One (inverseLimit A f) where
  one := ⟨1, fun n ↦ map_one (f n).hom⟩

/-- Pointwise addition of compatible families. -/
instance instAdd_inverseLimit : Add (inverseLimit A f) where
  add x y :=
    ⟨x.val + y.val, fun n ↦
      (map_add (f n).hom (x.val (n + 1)) (y.val (n + 1))).trans
        (congrArg₂ (· + ·) (x.property n) (y.property n))⟩

/-- Pointwise multiplication of compatible families. -/
instance instMul_inverseLimit : Mul (inverseLimit A f) where
  mul x y :=
    ⟨x.val * y.val, fun n ↦
      (map_mul (f n).hom (x.val (n + 1)) (y.val (n + 1))).trans
        (congrArg₂ (· * ·) (x.property n) (y.property n))⟩

/-- Pointwise negation of a compatible family. -/
instance instNeg_inverseLimit : Neg (inverseLimit A f) where
  neg x := ⟨-x.val, fun n ↦ (map_neg (f n).hom (x.val (n + 1))).trans
    (congrArg Neg.neg (x.property n))⟩

/-- Pointwise subtraction of compatible families. -/
instance instSub_inverseLimit : Sub (inverseLimit A f) where
  sub x y :=
    ⟨x.val - y.val, fun n ↦
      (map_sub (f n).hom (x.val (n + 1)) (y.val (n + 1))).trans
        (congrArg₂ (· - ·) (x.property n) (y.property n))⟩

/-- Pointwise natural-number coercion of a compatible family. -/
instance instNatCast_inverseLimit : NatCast (inverseLimit A f) where
  natCast n := ⟨n, fun m ↦ map_natCast (f m).hom n⟩

/-- Pointwise integer coercion of a compatible family. -/
instance instIntCast_inverseLimit : IntCast (inverseLimit A f) where
  intCast n := ⟨n, fun m ↦ map_intCast (f m).hom n⟩

/-- Pointwise natural powers of a compatible family. -/
instance instPow_inverseLimit : Pow (inverseLimit A f) ℕ where
  pow x n := ⟨x.val ^ n, fun m ↦ (map_pow (f m).hom (x.val (m + 1)) n).trans
    (congrArg (· ^ n) (x.property m))⟩

/-- Pointwise natural scalar multiplication on compatible families. -/
instance instSMulNat_inverseLimit : SMul ℕ (inverseLimit A f) where
  smul n x := ⟨n • x.val, fun m ↦ (map_nsmul (f m).hom n (x.val (m + 1))).trans
    (congrArg (n • ·) (x.property m))⟩

/-- Pointwise integer scalar multiplication on compatible families. -/
instance instSMulInt_inverseLimit : SMul ℤ (inverseLimit A f) where
  smul n x := ⟨n • x.val, fun m ↦ (map_zsmul (f m).hom n (x.val (m + 1))).trans
    (congrArg (n • ·) (x.property m))⟩

/-- The inverse limit is a commutative ring under pointwise operations. -/
instance instCommRing_inverseLimit : CommRing (inverseLimit A f) :=
  let toPi : inverseLimit A f → ∀ n, (A n).carrier := Subtype.val
  Subtype.val_injective.commRing toPi rfl rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Canonical componentwise `Λ`-algebra map into the inverse limit. -/
def algebraMap_inverseLimit : Λ →+* inverseLimit A f where
  toFun r := ⟨algebraMap Λ (∀ n, (A n).carrier) r, fun n ↦ (f n).hom.commutes r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- The inverse limit is a `Λ`-algebra under the componentwise structure. -/
instance instAlgebra_inverseLimit : Algebra Λ (inverseLimit A f) :=
  (algebraMap_inverseLimit A f).toAlgebra

/-- Canonical projection from the inverse limit onto the stage `A n`. -/
def proj (n : ℕ) : inverseLimit A f →ₐ[Λ] (A n).carrier where
  toFun x := x.val n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The stage-`n` projection reads the `n`th component of a compatible family. -/
theorem proj_apply (x : inverseLimit A f) (n : ℕ) :
    proj A f n x = x.val n := rfl

/-- Successor maps intertwine consecutive projections from the inverse limit. -/
theorem proj_comp (n : ℕ) :
    (f n).hom.comp (proj A f (n + 1)) = proj A f n := by
  ext x
  exact x.property n

/-- A compatible family is a unit if and only if each of its components is a unit. -/
theorem isUnit_inverseLimit_iff (x : inverseLimit A f) :
    IsUnit x ↔ ∀ n, IsUnit (proj A f n x) := by
  constructor
  · intro hx n
    exact hx.map (proj A f n)
  · intro hx
    classical
    let y : inverseLimit A f :=
      ⟨fun n ↦ ↑((hx n).unit⁻¹), fun n ↦ by
        have hu : Units.map (f n).hom.toMonoidHom (hx (n + 1)).unit = (hx n).unit := by
          apply Units.ext
          change (f n).hom ↑((hx (n + 1)).unit) = ↑((hx n).unit)
          exact ((congrArg (f n).hom (hx (n + 1)).unit_spec).trans
            (x.property n)).trans (hx n).unit_spec.symm
        exact congrArg (fun u : (A n).carrierˣ ↦ (↑(u⁻¹) : (A n).carrier)) hu⟩
    refine isUnit_iff_exists_inv.mpr ⟨y, ?_⟩
    apply Subtype.ext
    funext n
    change x.val n * ↑((hx n).unit⁻¹) = 1
    exact (congrArg (fun a : (A n).carrier ↦ a * ↑((hx n).unit⁻¹))
      (hx n).unit_spec.symm).trans (Units.mul_inv _)

/-- Local transition maps make invertibility at any stage equivalent to invertibility at zero. -/
theorem isUnit_proj_iff_zero (x : inverseLimit A f) (n : ℕ) :
    IsUnit (proj A f n x) ↔ IsUnit (proj A f 0 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      IsUnit (proj A f (n + 1) x) ↔
          IsUnit ((f n).hom (proj A f (n + 1) x)) :=
        (isUnit_map_iff (f n).hom _).symm
      _ ↔ IsUnit (proj A f n x) := by rw [show
        (f n).hom (proj A f (n + 1) x) = proj A f n x from x.property n]
      _ ↔ IsUnit (proj A f 0 x) := ih

/-- Each projection from the inverse limit is a local homomorphism. -/
instance instIsLocalHom_proj (n : ℕ) : IsLocalHom (proj A f n) where
  map_nonunit x hx := (isUnit_inverseLimit_iff A f x).mpr fun m ↦
    (isUnit_proj_iff_zero A f x m).mpr ((isUnit_proj_iff_zero A f x n).mp hx)

/-- Compatible families are precisely the tuples of values of the projections. -/
theorem mem_inverseLimit {x : ∀ n, (A n).carrier} :
    (∀ n, (f n).hom (x (n + 1)) = x n) ↔
      ∃ y : inverseLimit A f, ∀ n, proj A f n y = x n := by
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, fun _ ↦ rfl⟩
  · rintro ⟨y, hy⟩ n
    rw [← hy (n + 1), ← hy n]
    exact y.property n

/-- Two compatible families agree if all projections agree. -/
theorem inverseLimit_ext {x y : inverseLimit A f}
    (h : ∀ n, proj A f n x = proj A f n y) : x = y :=
  Subtype.ext (funext h)

/-- Surjective successor maps induce surjective projections from the inverse limit. -/
theorem proj_surjective (hf : ∀ n, Function.Surjective (f n).hom) (n : ℕ) :
    Function.Surjective (proj A f n) := by
  classical
  induction n generalizing A with
  | zero =>
    intro initial
    let family : ∀ n, (A n).carrier :=
      fun n ↦ Nat.rec (motive := fun n ↦ (A n).carrier) initial
        (fun n previous ↦ (hf n previous).choose) n
    exact ⟨⟨family, fun n ↦ (hf n (family n)).choose_spec⟩, rfl⟩
  | succ n ih =>
    intro initial
    obtain ⟨tail, htail⟩ :=
      ih (fun m ↦ A (m + 1)) (fun m ↦ f (m + 1)) (fun m ↦ hf (m + 1)) initial
    let family : ∀ m, (A m).carrier :=
      fun m ↦ Nat.casesOn m ((f 0).hom (tail.val 0)) (fun m ↦ tail.val m)
    refine ⟨⟨family, ?_⟩, htail⟩
    intro m
    cases m with
    | zero => rfl
    | succ m => exact tail.property m

/-- Kernel of the canonical projection `inverseLimit A f → A n`. -/
def ker (n : ℕ) : Ideal (inverseLimit A f) :=
  RingHom.ker (proj A f n).toRingHom

/-- Membership in `ker n` is vanishing of the stage-`n` projection. -/
theorem mem_ker {x : inverseLimit A f} {n : ℕ} :
    x ∈ ker A f n ↔ proj A f n x = 0 := Iff.rfl

/-- The inverse limit of local rings along local maps is local. -/
instance instIsLocalRing_inverseLimit : IsLocalRing (inverseLimit A f) := by
  letI : IsLocalHom (proj A f 0).toRingHom := ⟨(instIsLocalHom_proj A f 0).map_nonunit⟩
  exact (proj A f 0).toRingHom.domain_isLocalRing

/-- Lift a stage-zero element to a compatible family using surjective transition maps. -/
noncomputable def inverseLimitLift (hf : ∀ n, Function.Surjective (f n).hom)
    (initial : (A 0).carrier) : inverseLimit A f := by
  let family : ∀ n, (A n).carrier :=
    fun n ↦ Nat.rec (motive := fun n ↦ (A n).carrier) initial
      (fun n previous ↦ (hf n previous).choose) n
  exact ⟨family, fun n ↦ (hf n (family n)).choose_spec⟩

/-- The lift has the supplied stage-zero coordinate. -/
theorem inverseLimitLift_zero (hf : ∀ n, Function.Surjective (f n).hom)
    (initial : (A 0).carrier) :
    proj A f 0 (inverseLimitLift A f hf initial) = initial := rfl

/-- Lift a residue representative through the tower to define the inverse residue map. -/
noncomputable def inverseLimitResidueFieldInv
    (hf : ∀ n, Function.Surjective (f n).hom) (value : k) :
    ResidueField (inverseLimit A f) :=
  residue (inverseLimit A f)
    (inverseLimitLift A f hf
      (residue_surjective ((A 0).residueFieldIso.symm value)).choose)

/-- Lifting a residue representative is a right inverse to the stage-zero residue map. -/
theorem inverseLimitResidueFieldIso_right_inv
    (hf : ∀ n, Function.Surjective (f n).hom) :
    Function.RightInverse (inverseLimitResidueFieldInv A f hf)
      ((A 0).residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom (proj A f 0))) := by
  intro value
  change (A 0).residueFieldIso (residue (A 0).carrier
    (proj A f 0 (inverseLimitLift A f hf
      (residue_surjective ((A 0).residueFieldIso.symm value)).choose))) = value
  rw [inverseLimitLift_zero, (residue_surjective _).choose_spec]
  exact (A 0).residueFieldIso.apply_symm_apply value

/-- Lifting a residue representative is a left inverse to the stage-zero residue map. -/
theorem inverseLimitResidueFieldIso_left_inv
    (hf : ∀ n, Function.Surjective (f n).hom) :
    Function.LeftInverse (inverseLimitResidueFieldInv A f hf)
      ((A 0).residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom (proj A f 0))) := by
  intro value
  apply ((A 0).residueFieldIso.toAlgHom.comp
    (ResidueField.mapAlgHom (proj A f 0))).toRingHom.injective
  exact inverseLimitResidueFieldIso_right_inv A f hf _

/-- Residue identification of a surjective inverse limit via the stage-zero projection. -/
noncomputable def inverseLimitResidueFieldIso
    (hf : ∀ n, Function.Surjective (f n).hom) :
    ResidueField (inverseLimit A f) ≃ₐ[Λ] k :=
  { (A 0).residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom (proj A f 0)) with
    invFun := inverseLimitResidueFieldInv A f hf
    left_inv := inverseLimitResidueFieldIso_left_inv A f hf
    right_inv := inverseLimitResidueFieldIso_right_inv A f hf }

/-- The residue identification factors through the stage-zero residue map. -/
theorem inverseLimitResidueFieldIso_spec
    (hf : ∀ n, Function.Surjective (f n).hom) :
    (inverseLimitResidueFieldIso A f hf).toAlgHom =
      (A 0).residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (proj A f 0)) := rfl

end ArtinianLocalAlgCat
