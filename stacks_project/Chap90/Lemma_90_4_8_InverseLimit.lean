module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

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
    proj A f n x = x.val n := sorry

/-- Successor maps intertwine consecutive projections from the inverse limit. -/
theorem proj_comp (n : ℕ) :
    (f n).hom.comp (proj A f (n + 1)) = proj A f n := sorry

/-- Each projection from the inverse limit is a local homomorphism. -/
instance instIsLocalHom_proj (n : ℕ) : IsLocalHom (proj A f n) := sorry

/-- Compatible families are precisely the tuples of values of the projections. -/
theorem mem_inverseLimit {x : ∀ n, (A n).carrier} :
    (∀ n, (f n).hom (x (n + 1)) = x n) ↔
      ∃ y : inverseLimit A f, ∀ n, proj A f n y = x n := sorry

/-- Two compatible families agree if all projections agree. -/
theorem inverseLimit_ext {x y : inverseLimit A f}
    (h : ∀ n, proj A f n x = proj A f n y) : x = y := sorry

/-- Surjective successor maps induce surjective projections from the inverse limit. -/
theorem proj_surjective (hf : ∀ n, Function.Surjective (f n).hom) (n : ℕ) :
    Function.Surjective (proj A f n) := sorry

/-- Kernel of the canonical projection `inverseLimit A f → A n`. -/
def ker (n : ℕ) : Ideal (inverseLimit A f) :=
  RingHom.ker (proj A f n).toRingHom

/-- Membership in `ker n` is vanishing of the stage-`n` projection. -/
theorem mem_ker {x : inverseLimit A f} {n : ℕ} :
    x ∈ ker A f n ↔ proj A f n x = 0 := sorry

/-- The inverse limit of local rings along local maps is local. -/
instance instIsLocalRing_inverseLimit : IsLocalRing (inverseLimit A f) := sorry

/-- Residue identification of the inverse limit with `k`, via the stage-`0` projection. -/
noncomputable def inverseLimitResidueFieldIso :
    ResidueField (inverseLimit A f) ≃ₐ[Λ] k :=
  AlgEquiv.ofBijective
    ((A 0).residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom (proj A f 0))) sorry

/-- The residue identification factors as the stage-`0` residue map followed by
the residue identification of `A 0`. -/
theorem inverseLimitResidueFieldIso_spec :
    (inverseLimitResidueFieldIso A f).toAlgHom =
      (A 0).residueFieldIso.toAlgHom.comp
        (ResidueField.mapAlgHom (proj A f 0)) := sorry

end ArtinianLocalAlgCat
