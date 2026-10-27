/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Dual-number fibre products in `ArtinianLocalAlgCat`

The fibre product `A ×_k k[ε]` is the algebra pullback of the residue map of
`A` and the canonical map from the dual numbers to `k`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable (A : ArtinianLocalAlgCat Λ k)

/-- The algebra pullback of the residue map and the dual-number residue map is local. -/
instance instIsLocalRing_dualNumberPullback :
    IsLocalRing (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) :=
  @AlgHom.isLocalRing_pullback _ _ _ _ _ _ _ _ _ _ _ _
    (toResidue A).hom (dualNumberToResidue Λ k).hom
    (dualNumberToResidue Λ k).isLocalHom

/-- The algebra pullback of the residue map and the dual-number residue map is Artinian. -/
instance instIsArtinianRing_dualNumberPullback :
    IsArtinianRing (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) := by
  -- The pullback is the trivial square-zero extension of `A` by its residue field.
  letI : Module A.carrierᵐᵒᵖ k := Module.compHom k (algebraMap A.carrier k).op
  letI : IsCentralScalar A.carrier k :=
    ⟨fun a b => mul_comm b (algebraMap A.carrier k a)⟩
  letI : Module.Finite A.carrier k :=
    Module.Finite.of_surjective (Algebra.linearMap A.carrier k)
      (A.residueFieldIso.surjective.comp residue_surjective)
  letI : Module.Finite A.carrier (TrivSqZeroExt A.carrier k) :=
    inferInstanceAs (Module.Finite A.carrier (A.carrier × k))
  letI : IsArtinianRing (TrivSqZeroExt A.carrier k) :=
    IsArtinianRing.of_finite A.carrier _
  let f : TrivSqZeroExt A.carrier k →+*
      AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom :=
    { toFun := fun x => ⟨(x.fst, ⟨(toResidue A).hom x.fst, x.snd⟩), rfl⟩
      map_one' := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact TrivSqZeroExt.ext (map_one _) rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply TrivSqZeroExt.ext (map_mul _ _ _)
          change x.fst • y.snd + MulOpposite.op y.fst • x.snd =
            algebraMap A.carrier k x.fst * y.snd + x.snd * algebraMap A.carrier k y.fst
          simp only [op_smul_eq_smul, Algebra.smul_def]
          rw [mul_comm x.snd]
      map_zero' := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact TrivSqZeroExt.ext (map_zero _) rfl
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact TrivSqZeroExt.ext (map_add _ _ _) rfl }
  refine Function.Surjective.isArtinianRing (f := f) ?_
  intro p
  refine ⟨⟨p.val.1, p.val.2.snd⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact TrivSqZeroExt.ext p.property rfl

/-- The first projection from the algebra pullback is a local homomorphism. -/
instance instIsLocalHom_dualNumberPullbackFst :
    IsLocalHom (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom) := by
  let h : IsLocalHom ((toResidue A).hom.toRingHom.pullbackFst
      (dualNumberToResidue Λ k).hom.toRingHom) :=
    @RingHom.isLocalHom_pullbackFst _ _ _ _ _ _
    (toResidue A).hom.toRingHom (dualNumberToResidue Λ k).hom.toRingHom
    ⟨fun x hx => (dualNumberToResidue Λ k).isLocalHom.map_nonunit x hx⟩
  exact ⟨fun x hx => h.map_nonunit x hx⟩

/-- The second projection from the algebra pullback is a local homomorphism. -/
instance instIsLocalHom_dualNumberPullbackSnd :
    IsLocalHom (AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom) := by
  let h : IsLocalHom ((toResidue A).hom.toRingHom.pullbackSnd
      (dualNumberToResidue Λ k).hom.toRingHom) :=
    @RingHom.isLocalHom_pullbackSnd _ _ _ _ _ _
    (toResidue A).hom.toRingHom (dualNumberToResidue Λ k).hom.toRingHom
    ⟨fun x hx => (toResidue A).isLocalHom.map_nonunit x hx⟩
  exact ⟨fun x hx => h.map_nonunit x hx⟩

/-- The pair consisting of `a` and its constant dual-number residue lies in the pullback. -/
theorem dualNumberPullbackSectionHom_mem (a : A.carrier) :
    ((AlgHom.prod (AlgHom.id Λ A.carrier)
      (((inlAlgHom k k k).restrictScalars Λ).comp (toResidue A).hom)) a) ∈
      AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom := by
  rfl

/-- The constant-coefficient section into the algebra pullback. -/
noncomputable def dualNumberPullbackSectionHom :
    A.carrier →ₐ[Λ] AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom :=
  AlgHom.codRestrict
    (AlgHom.prod (AlgHom.id Λ A.carrier)
      (((inlAlgHom k k k).restrictScalars Λ).comp (toResidue A).hom))
    (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom)
    (dualNumberPullbackSectionHom_mem A)

/-- The constant-coefficient section is a local homomorphism. -/
instance instIsLocalHom_dualNumberPullbackSectionHom :
    IsLocalHom (dualNumberPullbackSectionHom A) := by
  refine ⟨fun x hx => ?_⟩
  exact hx.map (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom)

/-- The forward residue map of the pullback and its inverse candidate. -/
noncomputable def dualNumberPullbackResidueFieldIso_forward :
    ResidueField (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) →ₐ[Λ] k :=
  A.residueFieldIso.toAlgHom.comp
    (ResidueField.mapAlgHom
      (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom))

/-- The inverse residue map of the pullback and its inverse candidate. -/
noncomputable def dualNumberPullbackResidueFieldIso_backward :
    k →ₐ[Λ] ResidueField (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) :=
  (ResidueField.mapAlgHom (dualNumberPullbackSectionHom A)).comp
    A.residueFieldIso.symm.toAlgHom

/-- The forward and backward residue maps compose to the identity on `k`. -/
theorem dualNumberPullbackResidueFieldIso_left_inv :
    (dualNumberPullbackResidueFieldIso_forward A).comp
        (dualNumberPullbackResidueFieldIso_backward A) = AlgHom.id Λ k := by
  have hcomp :
      (ResidueField.mapAlgHom
        (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom)).comp
          (ResidueField.mapAlgHom (dualNumberPullbackSectionHom A)) =
        AlgHom.id Λ (ResidueField A.carrier) := by
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    rfl
  apply AlgHom.ext
  intro x
  change A.residueFieldIso
    (((ResidueField.mapAlgHom
      (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom)).comp
        (ResidueField.mapAlgHom (dualNumberPullbackSectionHom A)))
          (A.residueFieldIso.symm x)) = x
  rw [hcomp]
  exact A.residueFieldIso.apply_symm_apply x

/-- The backward and forward residue maps compose to the identity on the pullback residue field. -/
theorem dualNumberPullbackResidueFieldIso_right_inv :
    (dualNumberPullbackResidueFieldIso_backward A).comp
        (dualNumberPullbackResidueFieldIso_forward A) =
      AlgHom.id Λ (ResidueField (AlgHom.pullback (toResidue A).hom
        (dualNumberToResidue Λ k).hom)) := by
  apply AlgHom.ext
  intro x
  apply (dualNumberPullbackResidueFieldIso_forward A).toRingHom.injective
  exact DFunLike.congr_fun (dualNumberPullbackResidueFieldIso_left_inv A)
    (dualNumberPullbackResidueFieldIso_forward A x)

/-- The residue-field identification of the dual-number pullback. -/
noncomputable def dualNumberPullbackResidueFieldIso :
    ResidueField (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom (dualNumberPullbackResidueFieldIso_forward A)
    (dualNumberPullbackResidueFieldIso_backward A)
    (dualNumberPullbackResidueFieldIso_left_inv A)
    (dualNumberPullbackResidueFieldIso_right_inv A)

/-- The dual-number algebra pullback as an object of `ArtinianLocalAlgCat`. -/
noncomputable def dualNumberPullback : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom)
    (dualNumberPullbackResidueFieldIso A)

/-- The carrier of the bundled dual-number pullback is its algebra pullback. -/
theorem dualNumberPullback_carrier :
    (dualNumberPullback A).carrier =
      CommRingCat.of (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) := rfl

/-- The residue compatibility law for the first pullback projection. -/
theorem dualNumberPullbackFst_residue_compat :
    residueCompat (A := dualNumberPullback A) (B := A)
        (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom)
        (instIsLocalHom_dualNumberPullbackFst A) =
      residueIsoHom (dualNumberPullback A) := rfl

/-- The residue compatibility law for the second pullback projection. -/
theorem dualNumberPullbackSnd_residue_compat :
    residueCompat (A := dualNumberPullback A) (B := dualNumber Λ k)
        (AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom)
        (instIsLocalHom_dualNumberPullbackSnd A) =
      residueIsoHom (dualNumberPullback A) := by
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := residue_surjective x
  change p.val.2.fst = A.residueFieldIso (IsLocalRing.residue A.carrier p.val.1)
  exact p.property.symm

/-- The residue compatibility law for the constant-coefficient section. -/
theorem dualNumberPullbackSection_residue_compat :
    residueCompat (A := A) (B := dualNumberPullback A) (dualNumberPullbackSectionHom A)
        (instIsLocalHom_dualNumberPullbackSectionHom A) = residueIsoHom A := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  rfl

/-- The first pullback projection as a morphism of residue-identified algebras. -/
noncomputable def dualNumberPullbackFst : dualNumberPullback A ⟶ A :=
  Hom.of (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom)
    (instIsLocalHom_dualNumberPullbackFst A)
    (dualNumberPullbackFst_residue_compat A)

/-- The second pullback projection as a morphism of residue-identified algebras. -/
noncomputable def dualNumberPullbackSnd : dualNumberPullback A ⟶ dualNumber Λ k :=
  Hom.of (AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom)
    (instIsLocalHom_dualNumberPullbackSnd A)
    (dualNumberPullbackSnd_residue_compat A)

/-- The constant-coefficient section as a morphism of residue-identified algebras. -/
noncomputable def dualNumberPullbackSection : A ⟶ dualNumberPullback A :=
  Hom.of (dualNumberPullbackSectionHom A)
    (instIsLocalHom_dualNumberPullbackSectionHom A)
    (dualNumberPullbackSection_residue_compat A)

/-- The first pullback projection has the expected underlying algebra map. -/
theorem dualNumberPullbackFst_hom :
    (dualNumberPullbackFst A).hom =
      AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom := rfl

/-- The second pullback projection has the expected underlying algebra map. -/
theorem dualNumberPullbackSnd_hom :
    (dualNumberPullbackSnd A).hom =
      AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom := rfl

/-- The constant-coefficient section has the expected pullback projection law. -/
theorem dualNumberPullbackSection_comp_fst :
    dualNumberPullbackSection A ≫ dualNumberPullbackFst A = 𝟙 A := rfl

/-- The dual-number algebra pullback gives a pullback square in `ArtinianLocalAlgCat`. -/
theorem isPullback_dualNumberPullback :
    IsPullback (dualNumberPullbackFst A) (dualNumberPullbackSnd A)
      (toResidue A) (dualNumberToResidue Λ k) := by
  have hom_ext {B C : ArtinianLocalAlgCat Λ k} (f g : B ⟶ C)
      (h : f.hom = g.hom) : f = g := by
    rcases f with ⟨f, hf, hf'⟩
    rcases g with ⟨g, hg, hg'⟩
    cases h
    rfl
  have w : dualNumberPullbackFst A ≫ toResidue A =
      dualNumberPullbackSnd A ≫ dualNumberToResidue Λ k :=
    hom_ext _ _ (AlgHom.pullback_comm_sq _ _)
  let lift : ∀ s : Limits.PullbackCone (toResidue A) (dualNumberToResidue Λ k),
      s.pt ⟶ dualNumberPullback A := fun s => by
    let l : s.pt.carrier →ₐ[Λ]
        AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom :=
      AlgHom.codRestrict (AlgHom.prod s.fst.hom s.snd.hom) _ (by
        intro x
        change (toResidue A).hom (s.fst.hom x) = (dualNumberToResidue Λ k).hom (s.snd.hom x)
        exact congrArg (fun f : s.pt ⟶ residue Λ k => f.hom x) s.condition)
    have hl : IsLocalHom l := by
      refine ⟨fun x hx => ?_⟩
      exact s.fst.isLocalHom.map_nonunit x
        (hx.map (AlgHom.pullbackFst (toResidue A).hom (dualNumberToResidue Λ k).hom))
    have hr : residueCompat (B := dualNumberPullback A) l hl = residueIsoHom s.pt := by
      apply AlgHom.ext
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      exact DFunLike.congr_fun s.fst.residue_compat (IsLocalRing.residue s.pt.carrier a)
    exact Hom.of l hl hr
  apply IsPullback.of_isLimit
    (Limits.PullbackCone.IsLimit.mk w lift ?_ ?_ ?_)
  · intro s
    exact hom_ext _ _ (AlgHom.ext fun _ => rfl)
  · intro s
    exact hom_ext _ _ (AlgHom.ext fun _ => rfl)
  · intro s m hm₁ hm₂
    apply hom_ext
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (congrArg (fun f : s.pt ⟶ A => f.hom x) hm₁)
      (congrArg (fun f : s.pt ⟶ dualNumber Λ k => f.hom x) hm₂)

end ArtinianLocalAlgCat
