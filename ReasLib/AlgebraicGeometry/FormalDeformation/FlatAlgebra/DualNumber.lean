/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion

/-!
# Trivial dual-number lift of a ring deformation

The residue-fibre slice projection of `Def_P` and the trivial `k[ε]`-algebra
`P[ε] = DualNumber P`.
-/

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt
open scoped TensorProduct

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- `deformationForget` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (P : Type u) [CommRing P] [Algebra k P] :
    deformationForget Λ k P =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget := rfl

/-- The slice projection of `Def_P` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (P : Type u) [CommRing P] [Algebra k P] :
    IsPredeformationCategory (deformationForget Λ k P) :=
  CategoryTheory.Functor.instIsPredeformationCategory_overForget
    (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) (residueObj Λ k P)

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op
    (P : Type u) [CommRing P] [Algebra k P] :
    IsFibered.InGroupoids (deformationForget Λ k P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The constant inclusion of the residue field in its dual numbers is local. -/
private theorem residueToDualNumber_isLocalHom :
    IsLocalHom (inlAlgHom Λ k k) :=
  ⟨fun _ h ↦ isUnit_inl_iff.mp h⟩

/-- The constant inclusion preserves the chosen residue-field identifications. -/
private theorem residueToDualNumber_residue_compat :
    residueCompat (A := residue Λ k) (B := dualNumber Λ k)
      (inlAlgHom Λ k k) (residueToDualNumber_isLocalHom Λ k) =
        residueIsoHom (residue Λ k) := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

/-- The constant inclusion from the residue-field object into its dual numbers. -/
def residueToDualNumber : residue Λ k ⟶ dualNumber Λ k :=
  ArtinianLocalAlgCat.Hom.of (inlAlgHom Λ k k)
    (by exact residueToDualNumber_isLocalHom Λ k) (by exact residueToDualNumber_residue_compat Λ k)

/-- The constant inclusion sends a scalar to its constant dual number. -/
theorem residueToDualNumber_apply (a : (residue Λ k).carrier) :
    (residueToDualNumber Λ k).hom a = inl (a : k) := rfl

/-- The coefficientwise ring map from dual numbers over a field to dual numbers over an
algebra over that field. -/
def dualNumberRingHom (P : Type u) [CommRing P] [Algebra k P] :
    (dualNumber Λ k).carrier →+* DualNumber P :=
  (DualNumber.lift ⟨(Algebra.ofId k (DualNumber P), DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ ↦ DualNumber.commute_eps_left _⟩).toRingHom

/-- The coefficient ring map applies the algebra map to both coordinates. -/
theorem dualNumberRingHom_apply (P : Type u) [CommRing P] [Algebra k P]
    (x : (dualNumber Λ k).carrier) :
    dualNumberRingHom Λ k P x = ⟨algebraMap k P x.fst, algebraMap k P x.snd⟩ := by
  change inl (algebraMap k P x.fst) +
    inl (algebraMap k P x.snd) * DualNumber.eps = _
  ext <;> simp only [fst_add, fst_inl, fst_mul, DualNumber.fst_eps, mul_zero,
    add_zero, snd_add, snd_inl, DualNumber.snd_mul, DualNumber.snd_eps,
    mul_one, zero_add, fst_mk, snd_mk]

/-- `P[ε]` is a `k[ε]`-algebra via the coefficientwise algebra map. -/
instance instAlgebra_trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    Algebra (dualNumber Λ k).carrier (DualNumber P) :=
  (dualNumberRingHom Λ k P).toAlgebra

/-- The base-change identification has inverse `x ↦ 1 ⊗ x.fst + ε ⊗ x.snd`. -/
private def trivialTensorEquiv (P : Type u) [CommRing P] [Algebra k P]
    (ak : Algebra k (dualNumber Λ k).carrier)
    (hak : ∀ r, ak.algebraMap r = inl r) :
    letI := ak
    ((dualNumber Λ k).carrier ⊗[k] P) ≃ₗ[(dualNumber Λ k).carrier] DualNumber P := by
  letI := ak
  let eps : (dualNumber Λ k).carrier := DualNumber.eps
  letI : IsScalarTower k (dualNumber Λ k).carrier (DualNumber P) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      change inl (algebraMap k P a) = dualNumberRingHom Λ k P (ak.algebraMap a)
      rw [hak, dualNumberRingHom_apply]
      simp only [fst_inl, snd_inl, map_zero]
      rfl)
  let f : (dualNumber Λ k).carrier ⊗[k] P →ₐ[(dualNumber Λ k).carrier] DualNumber P :=
    AlgHom.liftEquiv k (dualNumber Λ k).carrier P (DualNumber P) (inlAlgHom k P P)
  let i : DualNumber P →ₗ[k] (dualNumber Λ k).carrier ⊗[k] P :=
    (TensorProduct.mk k (dualNumber Λ k).carrier P 1).comp (fstHom k P P).toLinearMap +
      (TensorProduct.mk k (dualNumber Λ k).carrier P eps).comp
        ((sndHom P P).restrictScalars k)
  have hf (a : (dualNumber Λ k).carrier) (p : P) :
      f (a ⊗ₜ[k] p) = ⟨algebraMap k P a.fst * p, algebraMap k P a.snd * p⟩ := by
    change dualNumberRingHom Λ k P a * inl p = _
    rw [dualNumberRingHom_apply]
    ext <;> simp
  refine { f.toLinearMap with invFun := i, left_inv := ?_, right_inv := ?_ }
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      change i (f (a ⊗ₜ[k] p)) = a ⊗ₜ[k] p
      rw [hf]
      change (1 : (dualNumber Λ k).carrier) ⊗ₜ[k] (algebraMap k P a.fst * p) +
        (eps : (dualNumber Λ k).carrier) ⊗ₜ[k] (algebraMap k P a.snd * p) = _
      rw [← Algebra.smul_def, ← Algebra.smul_def, ← TensorProduct.smul_tmul,
        ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
      congr 1
      simp only [Algebra.smul_def, hak]
      change inl a.fst * (1 : DualNumber k) + inl a.snd * DualNumber.eps = a
      apply TrivSqZeroExt.ext
      · change a.fst * 1 + a.snd * 0 = a.fst
        simp
      · change (a.fst * 0 + 0 * 1) + (a.snd * 1 + 0 * 0) = a.snd
        simp
    | add x y hx hy =>
      change i (f x) = x at hx
      change i (f y) = y at hy
      change i (f (x + y)) = x + y
      rw [_root_.map_add, _root_.map_add, hx, hy]
  · intro x
    change f ((1 : (dualNumber Λ k).carrier) ⊗ₜ[k] x.fst +
      (eps : (dualNumber Λ k).carrier) ⊗ₜ[k] x.snd) = x
    rw [_root_.map_add, hf, hf]
    change (⟨algebraMap k P 1 * x.fst, algebraMap k P 0 * x.fst⟩ : DualNumber P) +
      ⟨algebraMap k P 0 * x.snd, algebraMap k P 1 * x.snd⟩ = x
    apply TrivSqZeroExt.ext <;> simp

/-- `P[ε]` is flat as a module over `k[ε]`. -/
instance instModuleFlat_trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    Module.Flat (dualNumber Λ k).carrier (DualNumber P) := by
  letI : Algebra k (dualNumber Λ k).carrier := inferInstanceAs (Algebra k (DualNumber k))
  exact Module.Flat.of_linearEquiv
    (trivialTensorEquiv Λ k P inferInstance (fun _ ↦ rfl)).symm

/-- The trivial dual-number object `(k[ε], P[ε])` of `FlatAlgebraCat`. -/
def trivialDeformationObj (P : Type u) [CommRing P] [Algebra k P] : FlatAlgebraCat Λ k :=
  of (dualNumber Λ k) (DualNumber P)

/-- The base of `trivialDeformationObj` is `k[ε]`. -/
theorem trivialDeformationObj_base (P : Type u) [CommRing P] [Algebra k P] :
    (trivialDeformationObj Λ k P).base = dualNumber Λ k := rfl

/-- The underlying algebra of `trivialDeformationObj` is `DualNumber P`. -/
theorem trivialDeformationObj_carrier (P : Type u) [CommRing P] [Algebra k P] :
    (trivialDeformationObj Λ k P).algebra = DualNumber P := rfl

/-- The trivial dual-number deformation of `x0 = (k, P)` in the fibre of `forget`. -/
def trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    forget.Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : forget.obj (trivialDeformationObj Λ k P) = dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialDeformationObj`. -/
theorem trivialDeformation_obj (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (trivialDeformation Λ k P) = trivialDeformationObj Λ k P := rfl

/-- The first projection on the trivial deformation commutes with the coefficient maps. -/
private theorem trivialDeformationToResidue_commutes
    (P : Type u) [CommRing P] [Algebra k P] :
    ((fstHom P P P).toRingHom).comp
        (algebraMap (trivialDeformationObj Λ k P).base.carrier
          (trivialDeformationObj Λ k P).algebra) =
      (algebraMap (ofResidue Λ k P).base.carrier (ofResidue Λ k P).algebra).comp
        (ArtinianLocalAlgCat.dualNumberToResidue Λ k).hom.toRingHom := by
  ext x
  exact congrArg TrivSqZeroExt.fst (dualNumberRingHom_apply Λ k P x)

/-- The first projection on the trivial deformation induces a base-change isomorphism. -/
private theorem trivialDeformationToResidue_isIsoTensor
    (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (canonicalTensorMap
      (Q := trivialDeformationObj Λ k P) (P := ofResidue Λ k P)
      (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (fstHom P P P).toRingHom
      (trivialDeformationToResidue_commutes Λ k P)) := by
  letI : Algebra (dualNumber Λ k).carrier k :=
    algebraAlong (Q := trivialDeformationObj Λ k P) (P := ofResidue Λ k P)
    (ArtinianLocalAlgCat.dualNumberToResidue Λ k)
  letI : Algebra (dualNumber Λ k).carrier (DualNumber P) :=
    instAlgebra_trivialDeformation Λ k P
  letI : SMul (dualNumber Λ k).carrier (DualNumber P) :=
    (instAlgebra_trivialDeformation Λ k P).toSMul
  letI : Module (dualNumber Λ k).carrier (DualNumber P) := Algebra.toModule
  let eps : (dualNumber Λ k).carrier := DualNumber.eps
  let f : k ⊗[(dualNumber Λ k).carrier] DualNumber P →ₐ[k] P := by
    letI : Algebra (dualNumber Λ k).carrier P :=
      compAlgebraAlong (Q := trivialDeformationObj Λ k P) (P := ofResidue Λ k P)
        (ArtinianLocalAlgCat.dualNumberToResidue Λ k)
    letI : IsScalarTower (dualNumber Λ k).carrier k P :=
      IsScalarTower.of_algebraMap_eq' rfl
    exact AlgHom.liftEquiv (dualNumber Λ k).carrier k (DualNumber P) P
      { (fstHom P P P).toRingHom with
        commutes' := fun r ↦ RingHom.congr_fun (trivialDeformationToResidue_commutes Λ k P) r }
  change Function.Bijective f
  let i : P → k ⊗[(dualNumber Λ k).carrier] DualNumber P :=
    fun p ↦ 1 ⊗ₜ[(dualNumber Λ k).carrier] inl p
  have heps (a : k) (p : P) : a ⊗ₜ[(dualNumber Λ k).carrier] (inr p : DualNumber P) = 0 := by
    have hinr : (inr p : DualNumber P) =
        (eps : (dualNumber Λ k).carrier) • (inl p : DualNumber P) := by
      change inr p = dualNumberRingHom Λ k P eps * inl p
      rw [dualNumberRingHom_apply]
      ext <;> simp [eps]
    rw [hinr, ← TensorProduct.smul_tmul]
    have hz : (eps : (dualNumber Λ k).carrier) • a = 0 := by
      change (0 : k) * a = 0
      exact zero_mul a
    rw [hz, TensorProduct.zero_tmul]
  have hi : Function.LeftInverse i f := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [i]
    | tmul a q =>
      change 1 ⊗ₜ[(dualNumber Λ k).carrier] inl (a • q.fst) =
        a ⊗ₜ[(dualNumber Λ k).carrier] q
      let scalar : (dualNumber Λ k).carrier := inl a
      have hsmul : scalar • (inl q.fst : DualNumber P) =
          inl (a • q.fst) := by
        change dualNumberRingHom Λ k P (inl a) * inl q.fst = inl (a • q.fst)
        rw [dualNumberRingHom_apply]
        ext <;> simp [Algebra.smul_def]
      rw [← hsmul, ← TensorProduct.smul_tmul]
      have ha : scalar • (1 : k) = a := by
        change a * 1 = a
        exact mul_one a
      rw [ha]
      conv_rhs => rw [← q.inl_fst_add_inr_snd_eq, TensorProduct.tmul_add, heps, add_zero]
    | add x y hx hy =>
      simpa [i, _root_.map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy
  have hr : Function.RightInverse i f := by
    intro p
    change (1 : k) • p = p
    exact one_smul k p
  exact ⟨hi.injective, hr.surjective⟩

/-- The morphism `(k[ε], P[ε]) ⟶ (k, P)` over the coefficient projection `k[ε] ⟶ k`. -/
def trivialDeformationToResidue (P : Type u) [CommRing P] [Algebra k P] :
    trivialDeformationObj Λ k P ⟶ ofResidue Λ k P :=
  Hom.of (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (fstHom P P P).toRingHom
    (by exact trivialDeformationToResidue_commutes Λ k P)
    (by exact trivialDeformationToResidue_isIsoTensor Λ k P)

/-- The base map of `trivialDeformationToResidue` is `dualNumberToResidue`. -/
theorem trivialDeformationToResidue_base (P : Type u) [CommRing P] [Algebra k P] :
    forget.map (trivialDeformationToResidue Λ k P) = ArtinianLocalAlgCat.dualNumberToResidue Λ k := rfl

/-- The constant inclusions commute with the coefficient algebra maps. -/
private theorem trivialPushforward_commutes (P : Type u) [CommRing P] [Algebra k P] :
    (inlHom P P).comp (algebraMap (ofResidue Λ k P).base.carrier (ofResidue Λ k P).algebra) =
      (algebraMap (trivialDeformationObj Λ k P).base.carrier (trivialDeformationObj Λ k P).algebra).comp
        (residueToDualNumber Λ k).hom.toRingHom := by
  apply RingHom.ext
  intro a
  change inl (algebraMap k P a) = dualNumberRingHom Λ k P (inl a)
  rw [dualNumberRingHom_apply]
  simp only [fst_inl, snd_inl, map_zero]
  rfl

/-- The constant inclusion on the trivial deformation induces a base-change isomorphism. -/
private theorem trivialPushforward_isIsoTensor
    (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (canonicalTensorMap
      (Q := ofResidue Λ k P) (P := trivialDeformationObj Λ k P)
      (residueToDualNumber Λ k) (inlHom P P)
      (trivialPushforward_commutes Λ k P)) := by
  let ak : Algebra k (dualNumber Λ k).carrier :=
    algebraAlong (Q := ofResidue Λ k P) (P := trivialDeformationObj Λ k P)
      (residueToDualNumber Λ k)
  let e := trivialTensorEquiv Λ k P ak (fun _ ↦ rfl)
  change Function.Bijective (e : _ → DualNumber P)
  exact e.bijective

/-- The morphism `(k, P) ⟶ (k[ε], P[ε])` over the inclusion `k ⟶ k[ε]`. -/
def trivialPushforward (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (residueObj Λ k P) ⟶
      Fiber.fiberInclusion.obj (trivialDeformation Λ k P) :=
  Hom.of (residueToDualNumber Λ k) (inlHom P P)
    (by exact trivialPushforward_commutes Λ k P) (by exact trivialPushforward_isIsoTensor Λ k P)

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (P : Type u) [CommRing P] [Algebra k P] :
    forget.map (trivialPushforward Λ k P) = residueToDualNumber Λ k := rfl

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    (P : Type u) [CommRing P] [Algebra k P] :
    forget.IsStronglyCocartesian (residueToDualNumber Λ k) (trivialPushforward Λ k P) := by
  let p : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k := forget
  have opLift {R S : ArtinianLocalAlgCat Λ k} {X Y : FlatAlgebraCat Λ k}
      {f : R ⟶ S} {φ : X ⟶ Y} (h : p.IsHomLift f φ) :
      p.op.IsHomLift f.op φ.op := by
    cases h
    exact IsHomLift.map _
  have unopLift {R S : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {X Y : (FlatAlgebraCat Λ k)ᵒᵖ}
      {f : R ⟶ S} {φ : X ⟶ Y} (h : p.op.IsHomLift f φ) :
      p.IsHomLift f.unop φ.unop := by
    cases h
    exact IsHomLift.map _
  have hc := IsFibered.isStronglyCartesian_of_isCartesian p.op
    (p.op.map (trivialPushforward Λ k P).op) (trivialPushforward Λ k P).op
  refine { toIsHomLift := IsHomLift.map (trivialPushforward Λ k P), universal_property' := ?_ }
  intro Y g ψ hψ
  have hop : p.op.IsHomLift (g.op ≫ (residueToDualNumber Λ k).op) ψ.op := by
    simpa only [op_comp] using opLift hψ
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ :=
    @IsStronglyCartesian.universal_property' _ _ _ _ p.op _ _ _ _
      (p.op.map (trivialPushforward Λ k P).op) (trivialPushforward Λ k P).op
      hc (Opposite.op Y) g.op ψ.op hop
  refine ⟨χ.unop, ⟨unopLift hχ, congrArg Quiver.Hom.unop hfac⟩, ?_⟩
  intro χ' hχ'
  apply Quiver.Hom.op_inj
  exact huniq χ'.op ⟨opLift hχ'.1, congrArg Quiver.Hom.op hχ'.2⟩

/-- The trivial deformation as an object of the residue-fibre slice `Def_P`. -/
def trivialDeformationOver (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P :=
  Over.mk (trivialDeformationToResidue Λ k P)

/-- The trivial deformation in the dual-number fibre of `deformationForget`. -/
def trivialDeformationFiber (P : Type u) [CommRing P] [Algebra k P] :
    (deformationForget Λ k P).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k P).obj (trivialDeformationOver Λ k P) = dualNumber Λ k)

/-- The underlying Over-object of `trivialDeformationFiber` is `trivialDeformationOver`. -/
theorem trivialDeformationFiber_obj (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (trivialDeformationFiber Λ k P) =
      trivialDeformationOver Λ k P := rfl

end FlatAlgebraCat
