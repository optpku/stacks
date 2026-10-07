module

public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Quotients of objects of `C_Λ`

An ideal `J ≤ maximalIdeal B.carrier` yields an object `B.quotient J hJ` of
`ArtinianLocalAlgCat Λ k`, together with the canonical projection from `B` and
the factorisation of a morphism `f : B ⟶ A` through `B ⧸ J` whenever
`J ≤ RingHom.ker f.hom.toRingHom`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The kernel of a morphism in `ArtinianLocalAlgCat` is contained in the source
maximal ideal. -/
theorem ker_le_maximal {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    RingHom.ker f.hom.toRingHom ≤ maximalIdeal B.carrier :=
  le_maximalIdeal (RingHom.ker_ne_top f.hom.toRingHom)

/-- The quotient of an Artinian local algebra by an ideal contained in the maximal
ideal is nontrivial. -/
theorem nontrivial_quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : Nontrivial (B.carrier ⧸ J) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (mt (fun h ↦ eq_top_iff.2 (h.symm.trans_le hJ)) (Ideal.IsMaximal.ne_top inferInstance))

/-- The quotient of an Artinian local algebra by an ideal contained in the maximal
ideal is local. -/
theorem isLocalRing_quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : IsLocalRing (B.carrier ⧸ J) :=
  @IsLocalRing.of_surjective' B.carrier (B.carrier ⧸ J) inferInstance inferInstance inferInstance
    (nontrivial_quotient B J hJ) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- The quotient of an Artinian local algebra by any ideal is Artinian. -/
theorem isArtinianRing_quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier) :
    IsArtinianRing (B.carrier ⧸ J) :=
  inferInstance

/-- Canonical residue identification of `B.carrier ⧸ J` with `k`. -/
noncomputable def quotientResidueFieldIso (B : ArtinianLocalAlgCat Λ k)
    (J : Ideal B.carrier) (hJ : J ≤ maximalIdeal B.carrier)
    (hloc : IsLocalRing (B.carrier ⧸ J)) :
    @ResidueField (B.carrier ⧸ J) inferInstance hloc ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (@IsLocalRing.map_maximalIdeal_of_surjective B.carrier (B.carrier ⧸ J)
        inferInstance inferInstance inferInstance hloc
        (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).symm).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ hJ).trans B.residueFieldIso)

/-- The quotient `B ⧸ J`, viewed as an object of `ArtinianLocalAlgCat Λ k`. -/
noncomputable def quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : ArtinianLocalAlgCat Λ k where
  carrier := B.carrier ⧸ J
  isLocalRing := isLocalRing_quotient B J hJ
  isArtinianRing := isArtinianRing_quotient B J
  residueFieldIso := quotientResidueFieldIso B J hJ (isLocalRing_quotient B J hJ)

/-- The carrier of `B.quotient J hJ` is the ideal quotient `B.carrier ⧸ J`. -/
theorem quotient_carrier (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    (B.quotient J hJ).carrier = (B.carrier ⧸ J) := sorry

/-- A quotient in `ArtinianLocalAlgCat` is Artinian local, and its residue
identification is `quotientResidueFieldIso`. -/
theorem quotient_spec (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    IsArtinianRing (B.quotient J hJ).carrier ∧ IsLocalRing (B.quotient J hJ).carrier ∧
      (B.quotient J hJ).residueFieldIso =
        quotientResidueFieldIso B J hJ (isLocalRing_quotient B J hJ) := sorry

/-- Canonical projection `B ⟶ B ⧸ J` in `ArtinianLocalAlgCat`. -/
noncomputable def quotientMk (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : B ⟶ B.quotient J hJ where
  hom := Ideal.Quotient.mkₐ Λ J
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `quotientMk` is the canonical quotient map. -/
theorem quotientMk_hom (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    (quotientMk B J hJ).hom = Ideal.Quotient.mkₐ Λ J := sorry

/-- The factorisation `B ⧸ J ⟶ A` of a morphism `f : B ⟶ A` through the quotient by
an ideal contained in the kernel. -/
noncomputable def quotientFactor {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    B.quotient J (hJ.trans (ker_le_maximal f)) ⟶ A where
  hom := Ideal.Quotient.liftₐ J f.hom fun a ha ↦ RingHom.mem_ker.mp (hJ ha)
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `quotientFactor` is the induced map on quotients. -/
theorem quotientFactor_hom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    (quotientFactor f J hJ).hom =
      Ideal.Quotient.liftₐ J f.hom fun a ha ↦ RingHom.mem_ker.mp (hJ ha) := sorry

/-- The canonical projection and factorisation recover `f`. -/
theorem quotientFactor_comp_mk {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    quotientMk B J (hJ.trans (ker_le_maximal f)) ≫ quotientFactor f J hJ = f := sorry

end ArtinianLocalAlgCat
