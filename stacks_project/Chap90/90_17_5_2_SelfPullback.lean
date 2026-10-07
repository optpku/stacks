module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Self fibre products in `ArtinianLocalAlgCat`

The fibre product `A' ×_A A'` of a morphism `f : A' ⟶ A` with itself is the algebra
pullback of `f.hom` along itself, bundled as an object of `C_Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A' : ArtinianLocalAlgCat Λ k}

/-- The fibre product `A' ×_A A'` is a local ring. -/
instance instIsLocalRing_selfPullback (f : A' ⟶ A) :
    IsLocalRing (AlgHom.pullback f.hom f.hom) :=
  AlgHom.isLocalRing_pullback _ _

/-- The fibre product `A' ×_A A'` is Artinian. -/
instance instIsArtinianRing_selfPullback (f : A' ⟶ A) :
    IsArtinianRing (AlgHom.pullback f.hom f.hom) := sorry

/-- The first algebra projection of `A' ×_A A'` is local. -/
instance instIsLocalHom_selfPullbackFst (f : A' ⟶ A) :
    IsLocalHom (AlgHom.pullbackFst f.hom f.hom) := sorry

/-- The second algebra projection of `A' ×_A A'` is local. -/
instance instIsLocalHom_selfPullbackSnd (f : A' ⟶ A) :
    IsLocalHom (AlgHom.pullbackSnd f.hom f.hom) := sorry

/-- The diagonal algebra map `A' → A' ×_A A'`, sending `a` to `(a, a)`. -/
noncomputable def selfPullbackDiagonalHom (f : A' ⟶ A) :
    A'.carrier →ₐ[Λ] AlgHom.pullback f.hom f.hom :=
  AlgHom.codRestrict
    (AlgHom.prod (AlgHom.id Λ A'.carrier) (AlgHom.id Λ A'.carrier))
    (AlgHom.pullback f.hom f.hom) sorry

/-- The diagonal algebra map of `A' ×_A A'` is local. -/
instance instIsLocalHom_selfPullbackDiagonalHom (f : A' ⟶ A) :
    IsLocalHom (selfPullbackDiagonalHom f) := sorry

/-- Residue-field identification of `A' ×_A A'` with `k`, via the first projection
and the residue identification of `A'`. -/
noncomputable def selfPullbackResidueFieldIso (f : A' ⟶ A) :
    ResidueField (AlgHom.pullback f.hom f.hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    (A'.residueFieldIso.toAlgHom.comp
      (ResidueField.mapAlgHom (AlgHom.pullbackFst f.hom f.hom)))
    ((ResidueField.mapAlgHom (selfPullbackDiagonalHom f)).comp
      A'.residueFieldIso.symm.toAlgHom)
    sorry sorry

/-- The fibre product `A' ×_A A'`, viewed as an object of `ArtinianLocalAlgCat`. -/
noncomputable def selfPullback (f : A' ⟶ A) : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback f.hom f.hom) (selfPullbackResidueFieldIso f)

/-- The bundled self fibre product has the algebra-pullback carrier. -/
theorem selfPullback_carrier (f : A' ⟶ A) :
    (selfPullback f).carrier = AlgHom.pullback f.hom f.hom := sorry

/-- The first projection `A' ×_A A' ⟶ A'`. -/
noncomputable def selfPullbackFst (f : A' ⟶ A) : selfPullback f ⟶ A' where
  hom := AlgHom.pullbackFst f.hom f.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The second projection `A' ×_A A' ⟶ A'`. -/
noncomputable def selfPullbackSnd (f : A' ⟶ A) : selfPullback f ⟶ A' where
  hom := AlgHom.pullbackSnd f.hom f.hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The composite `A' ×_A A' ⟶ A` of either projection with `f`. -/
noncomputable def selfPullbackToBase (f : A' ⟶ A) : selfPullback f ⟶ A :=
  selfPullbackFst f ≫ f

/-- The diagonal section `A' ⟶ A' ×_A A'` of the two projections. -/
noncomputable def selfPullbackDiagonal (f : A' ⟶ A) : A' ⟶ selfPullback f where
  hom := selfPullbackDiagonalHom f
  isLocalHom := sorry
  residue_compat := sorry

/-- The induced map into `A' ×_A A'` from a pair of maps to `A'` that agree after `f`. -/
noncomputable def selfPullbackLift {B : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (g₁ g₂ : B ⟶ A') (h : g₁ ≫ f = g₂ ≫ f) : B ⟶ selfPullback f where
  hom :=
    AlgHom.codRestrict (AlgHom.prod g₁.hom g₂.hom) (AlgHom.pullback f.hom f.hom) sorry
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `selfPullbackFst` is the first algebra projection. -/
theorem selfPullbackFst_hom (f : A' ⟶ A) :
    (selfPullbackFst f).hom = AlgHom.pullbackFst f.hom f.hom := sorry

/-- The underlying algebra map of `selfPullbackSnd` is the second algebra projection. -/
theorem selfPullbackSnd_hom (f : A' ⟶ A) :
    (selfPullbackSnd f).hom = AlgHom.pullbackSnd f.hom f.hom := sorry

/-- The map to the base is the first projection followed by `f`. -/
theorem selfPullbackToBase_eq (f : A' ⟶ A) :
    selfPullbackToBase f = selfPullbackFst f ≫ f := sorry

/-- The two projections of `A' ×_A A'` agree after composing with `f`. -/
theorem selfPullbackFst_comp_eq_snd_comp (f : A' ⟶ A) :
    selfPullbackFst f ≫ f = selfPullbackSnd f ≫ f := sorry

/-- The second projection followed by `f` is the map from the self fibre product to the base. -/
theorem selfPullbackSnd_comp_eq_toBase (f : A' ⟶ A) :
    selfPullbackSnd f ≫ f = selfPullbackToBase f := sorry

/-- The diagonal is a section of the first projection. -/
theorem selfPullbackDiagonal_comp_fst (f : A' ⟶ A) :
    selfPullbackDiagonal f ≫ selfPullbackFst f = 𝟙 A' := sorry

/-- The diagonal is a section of the second projection. -/
theorem selfPullbackDiagonal_comp_snd (f : A' ⟶ A) :
    selfPullbackDiagonal f ≫ selfPullbackSnd f = 𝟙 A' := sorry

/-- The induced lift projects to the first given map. -/
theorem selfPullbackLift_comp_fst {B : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (g₁ g₂ : B ⟶ A') (h : g₁ ≫ f = g₂ ≫ f) :
    selfPullbackLift f g₁ g₂ h ≫ selfPullbackFst f = g₁ := sorry

/-- The induced lift projects to the second given map. -/
theorem selfPullbackLift_comp_snd {B : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (g₁ g₂ : B ⟶ A') (h : g₁ ≫ f = g₂ ≫ f) :
    selfPullbackLift f g₁ g₂ h ≫ selfPullbackSnd f = g₂ := sorry

/-- The self-cospan square is a pullback in `ArtinianLocalAlgCat`. -/
theorem isPullback_selfPullback (f : A' ⟶ A) :
    IsPullback (selfPullbackFst f) (selfPullbackSnd f) f f := sorry

/-- The self fibre product is a pullback cone for `f, f`, and its map to the base is
the composite of the first projection with `f`. -/
theorem selfPullback_spec (f : A' ⟶ A) :
    IsPullback (selfPullbackFst f) (selfPullbackSnd f) f f ∧
      selfPullbackToBase f = selfPullbackFst f ≫ f := sorry

end ArtinianLocalAlgCat
