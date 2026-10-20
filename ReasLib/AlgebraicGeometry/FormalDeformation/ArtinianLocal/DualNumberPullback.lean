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
    IsArtinianRing (AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom) := sorry

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
      AlgHom.pullback (toResidue A).hom (dualNumberToResidue Λ k).hom := sorry

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
    IsLocalHom (dualNumberPullbackSectionHom A) := sorry

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
        (dualNumberPullbackResidueFieldIso_backward A) = AlgHom.id Λ k := sorry

/-- The backward and forward residue maps compose to the identity on the pullback residue field. -/
theorem dualNumberPullbackResidueFieldIso_right_inv :
    (dualNumberPullbackResidueFieldIso_backward A).comp
        (dualNumberPullbackResidueFieldIso_forward A) =
      AlgHom.id Λ (ResidueField (AlgHom.pullback (toResidue A).hom
        (dualNumberToResidue Λ k).hom)) := sorry

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
      residueIsoHom (dualNumberPullback A) := sorry

/-- The residue compatibility law for the second pullback projection. -/
theorem dualNumberPullbackSnd_residue_compat :
    residueCompat (A := dualNumberPullback A) (B := dualNumber Λ k)
        (AlgHom.pullbackSnd (toResidue A).hom (dualNumberToResidue Λ k).hom)
        (instIsLocalHom_dualNumberPullbackSnd A) =
      residueIsoHom (dualNumberPullback A) := sorry

/-- The residue compatibility law for the constant-coefficient section. -/
theorem dualNumberPullbackSection_residue_compat :
    residueCompat (A := A) (B := dualNumberPullback A) (dualNumberPullbackSectionHom A)
        (instIsLocalHom_dualNumberPullbackSectionHom A) = residueIsoHom A := sorry

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
    dualNumberPullbackSection A ≫ dualNumberPullbackFst A = 𝟙 A := sorry

/-- The dual-number algebra pullback gives a pullback square in `ArtinianLocalAlgCat`. -/
theorem isPullback_dualNumberPullback :
    IsPullback (dualNumberPullbackFst A) (dualNumberPullbackSnd A)
      (toResidue A) (dualNumberToResidue Λ k) := sorry

end ArtinianLocalAlgCat
