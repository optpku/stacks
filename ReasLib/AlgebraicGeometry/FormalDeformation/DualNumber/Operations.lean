module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Section

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (Λ)


namespace ArtinianLocalAlgCat

noncomputable section

/-- Dual-number scaling `a + v ε ↦ a + (c v) ε` as a morphism of `C_Λ`. -/
def dualNumberScaleHom (c : k) : dualNumber Λ k ⟶ dualNumber Λ k := by
  let scale : DualNumber k → DualNumber k := fun value ↦ ⟨value.fst, c * value.snd⟩
  have laws :
      scale 1 = 1 ∧ (∀ left right, scale (left * right) = scale left * scale right) ∧
      scale 0 = 0 ∧ (∀ left right, scale (left + right) = scale left + scale right) ∧
      (∀ scalar : Λ, scale (algebraMap Λ (DualNumber k) scalar) = algebraMap Λ (DualNumber k) scalar) ∧
      (∀ hom : (dualNumber Λ k).carrier →ₐ[Λ] (dualNumber Λ k).carrier,
        (∀ value, hom value = scale value) →
        IsLocalHom hom ∧ ∀ localness : IsLocalHom hom,
          residueCompat hom localness = residueIsoHom (dualNumber Λ k)) := sorry
  let hom : (dualNumber Λ k).carrier →ₐ[Λ] (dualNumber Λ k).carrier :=
    { toFun := scale
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2.1
      commutes' := laws.2.2.2.2.1 }
  have compatibility := laws.2.2.2.2.2 hom (fun _ ↦ rfl)
  exact Hom.of hom compatibility.1 (compatibility.2 compatibility.1)

/-- Dual-number scaling evaluates to `(x.fst, c * x.snd)`. -/
theorem dualNumberScaleHom_apply (c : k) (x : (dualNumber Λ k).carrier) :
    (dualNumberScaleHom Λ c).hom x = ⟨x.fst, c * x.snd⟩ := rfl

/-- The coefficient projection is a local homomorphism. -/
instance instIsLocalHom_dualNumberToResidue :
    IsLocalHom
      ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier) :=
  (dualNumberToResidue Λ k).isLocalHom

/-- The fibre product `k[ε] ×_k k[ε]` is a local ring. -/
instance instIsLocalRing_dualNumberSelfPullback :
    IsLocalRing
      (AlgHom.pullback
        ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        ((dualNumberToResidue Λ k).hom)) :=
  AlgHom.isLocalRing_pullback
    ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
    ((dualNumberToResidue Λ k).hom)

/-- The fibre product `k[ε] ×_k k[ε]` is Artinian. -/
instance instIsArtinianRing_dualNumberSelfPullback :
    IsArtinianRing
      (AlgHom.pullback
        ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        ((dualNumberToResidue Λ k).hom)) := sorry

/-- The canonical section of the first projection `k[ε] → k[ε] ×_k k[ε]`,
sending `a + b ε` to `(a + b ε, a)`. -/
def dualNumberSelfPullbackSectionHom :
    (dualNumber Λ k).carrier →ₐ[Λ]
      AlgHom.pullback
        ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        ((dualNumberToResidue Λ k).hom) := by
  let hom := AlgHom.prod (AlgHom.id Λ (dualNumber Λ k).carrier)
    (((inlAlgHom k k k).restrictScalars Λ).comp (dualNumberToResidue Λ k).hom)
  have membership : ∀ value, hom value ∈
      AlgHom.pullback (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom := sorry
  exact AlgHom.codRestrict hom
    (AlgHom.pullback (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom) membership

/-- The first projection of `k[ε] ×_k k[ε]` is a local homomorphism. -/
instance instIsLocalHom_dualNumberSelfPullbackFst :
    IsLocalHom
      (AlgHom.pullbackFst
        ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        ((dualNumberToResidue Λ k).hom)) := sorry

/-- The canonical section of `k[ε] ×_k k[ε]` is a local homomorphism. -/
instance instIsLocalHom_dualNumberSelfPullbackSectionHom :
    IsLocalHom
      (dualNumberSelfPullbackSectionHom Λ :
        (dualNumber Λ k).carrier →ₐ[Λ]
          AlgHom.pullback
            ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
            ((dualNumberToResidue Λ k).hom)) := sorry

/-- Residue-field identification of `k[ε] ×_k k[ε]` with `k`. -/
def dualNumberSelfPullbackResidueFieldIso :
    IsLocalRing.ResidueField
      (AlgHom.pullback
        ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        ((dualNumberToResidue Λ k).hom)) ≃ₐ[Λ] k := by
  let forward :=
    (dualNumber Λ k).residueFieldIso.toAlgHom.comp
      (IsLocalRing.ResidueField.mapAlgHom
        (AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom))
  let backward :=
    (IsLocalRing.ResidueField.mapAlgHom (dualNumberSelfPullbackSectionHom Λ)).comp
      (dualNumber Λ k).residueFieldIso.symm.toAlgHom
  have laws : forward.comp backward = AlgHom.id Λ k ∧
      backward.comp forward = AlgHom.id Λ _ := sorry
  exact AlgEquiv.ofAlgHom forward backward laws.1 laws.2

/-- The fibre product `k[ε] ×_k k[ε]` as an object of `C_Λ`. -/
def dualNumberSelfPullback : ArtinianLocalAlgCat Λ k :=
  ArtinianLocalAlgCat.of
    (AlgHom.pullback
      ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
      ((dualNumberToResidue Λ k).hom))
    (dualNumberSelfPullbackResidueFieldIso Λ)

/-- The bundled self-pullback has the algebra-pullback carrier. -/
theorem dualNumberSelfPullback_carrier :
    ((dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier : Type u) =
      (AlgHom.pullback
        ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        ((dualNumberToResidue Λ k).hom) : Type u) := rfl

/-- Dual-number addition on the algebra pullback `k[ε] ×_k k[ε]`. -/
def dualNumberAddAlgHom :
    AlgHom.pullback
        ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
        ((dualNumberToResidue Λ k).hom) →ₐ[Λ]
      (dualNumber Λ k).carrier := by
  let addition : AlgHom.pullback (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom →
      (dualNumber Λ k).carrier := fun pair ↦ ⟨pair.val.1.fst, pair.val.1.snd + pair.val.2.snd⟩
  have laws : addition 1 = 1 ∧
      (∀ left right, addition (left * right) = addition left * addition right) ∧
      addition 0 = 0 ∧ (∀ left right, addition (left + right) = addition left + addition right) ∧
      (∀ scalar : Λ, addition (algebraMap Λ _ scalar) = algebraMap Λ _ scalar) := sorry
  exact
    { toFun := addition
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2.1
      commutes' := laws.2.2.2.2 }

/-- Dual-number addition `k[ε] ×_k k[ε] ⟶ k[ε]`. -/
def dualNumberAddHom : dualNumberSelfPullback Λ ⟶ dualNumber Λ k := by
  let hom : (dualNumberSelfPullback Λ).carrier →ₐ[Λ] (dualNumber Λ k).carrier :=
    dualNumberAddAlgHom Λ
  have laws : IsLocalHom hom ∧ ∀ localness : IsLocalHom hom,
      residueCompat hom localness = residueIsoHom (dualNumberSelfPullback Λ) := sorry
  exact Hom.of hom laws.1 (laws.2 laws.1)

/-- Dual-number addition on a pair `(a + b ε, a + c ε)` is `a + (b + c) ε`. -/
theorem dualNumberAddHom_apply
    (p : AlgHom.pullback
      ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
      ((dualNumberToResidue Λ k).hom)) :
    dualNumberAddAlgHom Λ p =
      ⟨(AlgHom.pullbackFst
          ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
          ((dualNumberToResidue Λ k).hom) p).fst,
        (AlgHom.pullbackFst
            ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
            ((dualNumberToResidue Λ k).hom) p).snd +
          (AlgHom.pullbackSnd
            ((dualNumberToResidue Λ k).hom : (dualNumber Λ k).carrier →ₐ[Λ] (residue Λ k).carrier)
            ((dualNumberToResidue Λ k).hom) p).snd⟩ := rfl

/-- The first projection `k[ε] ×_k k[ε] ⟶ k[ε]` in `C_Λ`. -/
def dualNumberSelfPullbackFst : dualNumberSelfPullback Λ ⟶ dualNumber Λ k := by
  let hom : (dualNumberSelfPullback Λ).carrier →ₐ[Λ] (dualNumber Λ k).carrier :=
    AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom
  have laws : IsLocalHom hom ∧ ∀ localness : IsLocalHom hom,
      residueCompat hom localness = residueIsoHom (dualNumberSelfPullback Λ) := sorry
  exact Hom.of hom laws.1 (laws.2 laws.1)

/-- The second projection `k[ε] ×_k k[ε] ⟶ k[ε]` in `C_Λ`. -/
def dualNumberSelfPullbackSnd : dualNumberSelfPullback Λ ⟶ dualNumber Λ k := by
  let hom : (dualNumberSelfPullback Λ).carrier →ₐ[Λ] (dualNumber Λ k).carrier :=
    AlgHom.pullbackSnd (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom
  have laws : IsLocalHom hom ∧ ∀ localness : IsLocalHom hom,
      residueCompat hom localness = residueIsoHom (dualNumberSelfPullback Λ) := sorry
  exact Hom.of hom laws.1 (laws.2 laws.1)

/-- The two projections of `k[ε] ×_k k[ε]` agree after reducing to `k`. -/
theorem dualNumberSelfPullbackFst_comp_proj :
    (dualNumberSelfPullbackFst Λ ≫ dualNumberToResidue Λ k :
        dualNumberSelfPullback Λ ⟶ residue Λ k) =
      dualNumberSelfPullbackSnd Λ ≫ dualNumberToResidue Λ k := sorry


/-- The composite projection `k[ε] ×_k k[ε] ⟶ k` through the first factor. -/
def dualNumberSelfPullbackToResidue : dualNumberSelfPullback Λ ⟶ residue Λ k :=
  dualNumberSelfPullbackFst Λ ≫ dualNumberToResidue Λ k

/-- `dualNumberSelfPullbackToResidue` is the first projection followed by `dualNumberProj`. -/
theorem dualNumberSelfPullbackToResidue_eq :
    dualNumberSelfPullbackToResidue Λ =
      (dualNumberSelfPullbackFst Λ ≫ dualNumberToResidue Λ k :
        dualNumberSelfPullback Λ ⟶ residue Λ k) := rfl


end

end ArtinianLocalAlgCat
