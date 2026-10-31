/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Finiteness.Projective
public import ReasLib.GroupTheory.MonoidExtension.Nat

/-!
# Restriction and linear actions for monoid-algebra modules

Scalar restriction along an extension inclusion is explicit. Restriction to subgroup
algebras and the resulting centralizer-linear action are canonical.
-/

@[expose] public section

noncomputable section

universe u v w x

open scoped MonoidAlgebra

namespace MonoidAlgebra

/-- The kernel-group action is the restriction of the monoid action along the extension inclusion. -/
class IsRestrictionAlongInl (Λ : Type u) {G : Type v} {Γ : Type w}
    [Ring Λ] [Group G] [Monoid Γ]
    (S : NatMonoidExtension G Γ) (P : Type x)
    [AddCommGroup P] [moduleGamma : Module (Λ[Γ]) P] [moduleG : Module (Λ[G]) P] : Prop where
  /-- Scalar multiplication agrees with the action pushed forward along the inclusion. -/
  smul_eq : ∀ (x : Λ[G]) (p : P), x • p = mapDomainRingHom Λ S.inl x • p

/-- Compatible scalar restriction agrees on group-algebra basis elements. -/
theorem IsRestrictionAlongInl.smul_single
    {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
    [Ring Λ] [Group G] [Monoid Γ]
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P]
    (S : NatMonoidExtension G Γ) [IsRestrictionAlongInl Λ S P] (g : G) (p : P) :
    (single g (1 : Λ) : Λ[G]) • p = (single (S.inl g) (1 : Λ) : Λ[Γ]) • p := by
  simpa [mapDomainRingHom_apply] using
    (IsRestrictionAlongInl.smul_eq (S := S) (single g (1 : Λ)) p)

variable {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
variable [Ring Λ] [Group G] [Monoid Γ]
variable [AddCommGroup P] [Module (Λ[Γ]) P]
variable (S : NatMonoidExtension G Γ)

/-- The module obtained by restricting scalars along an explicit extension inclusion. -/
@[reducible] def moduleRestrictInl : Module (Λ[G]) P :=
  Module.compHom P (mapDomainRingHom Λ S.inl)

/-- The explicitly restricted module has the canonical compatibility with its original action. -/
instance IsRestrictionAlongInl.instRestrictInl :
    IsRestrictionAlongInl Λ S P (moduleG := moduleRestrictInl S) :=
  IsRestrictionAlongInl.mk (moduleG := moduleRestrictInl S) (fun _ _ ↦ rfl)

variable [Module (Λ[G]) P]

/-- Restriction of a group-algebra module to a subgroup algebra. -/
instance moduleRestrictSubgroup (H : Subgroup G) : Module (Λ[H]) P :=
  Module.compHom P (mapDomainRingHom Λ H.subtype)

/-- Restriction to a subgroup algebra keeps the coefficient scalar tower. -/
instance isScalarTowerRestrictSubgroup (H : Subgroup G) [Module Λ P]
    [IsScalarTower Λ (Λ[G]) P] : IsScalarTower Λ (Λ[H]) P := by
  refine ⟨fun a x p => ?_⟩
  change (mapDomainRingHom Λ H.subtype (a • x)) • p =
    a • ((mapDomainRingHom Λ H.subtype x) • p)
  rw [← smul_assoc]
  congr 1
  simp [mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul]

/-- Finite generation over a finite group algebra persists on restriction to a subgroup algebra. -/
instance finiteRestrictSubgroup (H : Subgroup G) [Finite G]
    [Module.Finite (Λ[G]) P] : Module.Finite (Λ[H]) P := by
  letI : Module Λ P := Module.compHom P (singleOneRingHom (R := Λ) (M := G))
  letI : IsScalarTower Λ (Λ[G]) P := ⟨fun a x p ↦ by
    change (a • x) • p = (single (1 : G) a : Λ[G]) • (x • p)
    rw [← mul_smul]
    congr 1
    ext g
    simp [coeff_single_one_mul]⟩
  letI : Module.Finite Λ (Λ[G]) :=
    Module.Finite.equiv (MonoidAlgebra.basis G Λ).equivFun.symm
  haveI : Module.Finite Λ P := Module.Finite.trans (Λ[G]) P
  exact Module.Finite.of_restrictScalars_finite Λ (Λ[H]) P

/-- Finite projectivity over a finite group algebra persists on restriction to a subgroup algebra. -/
instance projectiveRestrictSubgroup (H : Subgroup G) [Finite G]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P] :
    Module.Projective (Λ[H]) P := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let eG : (Σ _ : G ⧸ H, H) ≃ G :=
    { toFun := fun z ↦ z.2.val * z.1.out⁻¹
      invFun := fun g ↦ ⟨((g⁻¹ : G) : G ⧸ H), ⟨g * ((g⁻¹ : G) : G ⧸ H).out, by
        simpa using H.inv_mem
          (QuotientGroup.eq.mp (QuotientGroup.out_eq' ((g⁻¹ : G) : G ⧸ H)))⟩⟩
      left_inv := by
        rintro ⟨q, h⟩
        have hq : (((h.val * q.out⁻¹)⁻¹ : G) : G ⧸ H) = q := by
          simpa [mul_inv_rev] using
            (QuotientGroup.mk_mul_of_mem q.out (H.inv_mem h.property)).trans
              (QuotientGroup.out_eq' q)
        apply Sigma.ext hq
        apply heq_of_eq
        apply Subtype.ext
        dsimp
        rw [hq]
        simp [mul_assoc]
      right_inv := fun g ↦ by simp [mul_assoc] }
  have heG (q : G ⧸ H) (h : H) : eG ⟨q, h⟩ = h.val * q.out⁻¹ := by
    rfl
  let eΛ : Λ[G] ≃ₗ[Λ] (G ⧸ H → Λ[H]) :=
    (MonoidAlgebra.basis G Λ).equivFun ≪≫ₗ
      LinearEquiv.piCongrLeft Λ (fun _ : (Σ _ : G ⧸ H, H) ↦ Λ) eG.symm ≪≫ₗ
      LinearEquiv.piCurry Λ (fun (_ : G ⧸ H) (_ : H) ↦ Λ) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ : G ⧸ H ↦ (MonoidAlgebra.basis H Λ).equivFun.symm)
  have heΛ (x : Λ[G]) (q : G ⧸ H) (h : H) :
      (eΛ x q).coeff h = x.coeff (h.val * q.out⁻¹) := by
    simp [eΛ, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
      Module.Basis.equivFun, MonoidAlgebra.basis, Equiv.piCongrLeft', Sigma.curry, heG]
  let e : Λ[G] ≃ₗ[Λ[H]] (G ⧸ H → Λ[H]) :=
    { eΛ.toAddEquiv with
      map_smul' := by
        intro a x
        change eΛ (a • x) = a • eΛ x
        induction a using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [add_smul, map_add, ha, hb]
        | single h r =>
          ext q k
          change (eΛ ((mapDomainRingHom Λ H.subtype (single h r)) * x) q).coeff k =
            (single h r * eΛ x q).coeff k
          simp [heΛ, mapDomainRingHom_apply, mul_assoc] }
  letI : Module.Free (Λ[H]) (Λ[G]) := Module.Free.of_equiv e.symm
  letI : IsScalarTower (Λ[H]) (Λ[G]) (Λ[G]) :=
    ⟨fun a x y ↦ mul_assoc (mapDomainRingHom Λ H.subtype a) x y⟩
  letI : IsScalarTower (Λ[H]) (Λ[G]) P :=
    ⟨fun a x p ↦ mul_smul (mapDomainRingHom Λ H.subtype a) x p⟩
  obtain ⟨n, f, g, _, _, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (Λ[G]) P
  letI : Module.Projective (Λ[H]) (Fin n → Λ[G]) := Module.Projective.of_free
  exact Module.Projective.of_split (g.restrictScalars (Λ[H]))
    (f.restrictScalars (Λ[H])) (by
      ext p
      exact DFunLike.congr_fun hfg p)

end MonoidAlgebra

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
variable [Ring Λ] [Group G] [Monoid Γ]
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module Λ P]

/-- The action of a monoid-algebra basis element preserves addition. -/
theorem smulEnd_map_add [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) (p q : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (p + q) =
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p +
        (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • q := by
  exact smul_add _ p q

/-- The action of a monoid-algebra basis element commutes with coefficient scalars. -/
theorem smulEnd_map_smul [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) (a : Λ) (p : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (a • p) =
      a • ((MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p) := by
  have h (q : P) : a • q = (MonoidAlgebra.single (1 : Γ) a : Λ[Γ]) • q := by
    calc
      a • q = (a • (1 : Λ[Γ])) • q := by rw [smul_assoc, one_smul]
      _ = _ := by simp [MonoidAlgebra.one_def]
  rw [h p, h ((MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p), ← mul_smul,
    ← mul_smul]
  simp

/-- The coefficient-linear action of a monoid element on a monoid-algebra module. -/
def smulEnd [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) : Module.End Λ P where
  toFun p := (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p
  map_add' := smulEnd_map_add γ
  map_smul' := smulEnd_map_smul γ

/-- The coefficient-linear action evaluates as multiplication by the corresponding basis element. -/
theorem smulEnd_apply [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) (p : P) :
    (smulEnd γ : Module.End Λ P) p = (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p := by
  rfl

variable [Module (Λ[G]) P]
variable (S : NatMonoidExtension G Γ)

/-- The action of a monoid element preserves addition when viewed over its centralizer algebra. -/
theorem smulEndZ_map_add [MonoidAlgebra.IsRestrictionAlongInl Λ S P]
    (γ : Γ) (p q : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (p + q) =
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p +
        (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • q := by
  exact smul_add _ p q

/-- The action of a monoid element commutes with scalars from its kernel-group centralizer algebra. -/
theorem smulEndZ_map_smul [MonoidAlgebra.IsRestrictionAlongInl Λ S P]
    (γ : Γ) (a : Λ[S.centralizer γ]) (p : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (a • p) =
      a • ((MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p) := by
  have h (b : Λ[S.centralizer γ]) :
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) *
          MonoidAlgebra.mapDomainRingHom Λ S.inl
            (MonoidAlgebra.mapDomainRingHom Λ (S.centralizer γ).subtype b) =
        MonoidAlgebra.mapDomainRingHom Λ S.inl
            (MonoidAlgebra.mapDomainRingHom Λ (S.centralizer γ).subtype b) *
          (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) := by
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc => simp only [map_add, mul_add, add_mul, hb, hc]
    | single g r =>
      simpa [MonoidAlgebra.mapDomainRingHom_apply] using
        congrArg (fun δ : Γ ↦ (MonoidAlgebra.single δ r : Λ[Γ])) g.property.symm
  change (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) •
      ((MonoidAlgebra.mapDomainRingHom Λ (S.centralizer γ).subtype a : Λ[G]) • p) =
    (MonoidAlgebra.mapDomainRingHom Λ (S.centralizer γ).subtype a : Λ[G]) •
      ((MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p)
  rw [MonoidAlgebra.IsRestrictionAlongInl.smul_eq (S := S),
    MonoidAlgebra.IsRestrictionAlongInl.smul_eq (S := S), ← mul_smul, ← mul_smul, h]

/-- The centralizer-algebra-linear action of a monoid element. -/
def smulEndZ [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : Γ) :
    Module.End (Λ[S.centralizer γ]) P where
  toFun p := (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p
  map_add' := smulEndZ_map_add S γ
  map_smul' := smulEndZ_map_smul S γ

/-- The centralizer-linear action evaluates as multiplication by the corresponding basis element. -/
theorem smulEndZ_apply [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : Γ) (p : P) :
    (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) P) p =
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p := by
  rfl

end LinearMap.FiniteProjective
