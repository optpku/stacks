module

public import stacks_project.Chap90.Lemma_90_10_8_Pullback
public import stacks_project.Chap90.«90_17_5_3_Pullback»
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension

/-!
# Comparison map `A1 ×_A A2 ⟶ k[I]`

For a small extension `f2 : A2 ⟶ A` with a section `h : A1 ⟶ A2` of the cospan,
the map `g(u, v) = residue(u) ⊕ (v - h(u))` is a morphism of `C_Λ` from the fibre
product to `k[I]`, and `(u, v) ↦ (u, g(u, v))` identifies `A1 ×_A A2` with
`A1 ×_k k[I]`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A1 A2 : ArtinianLocalAlgCat Λ k}

/-- The difference `v - h(u)` of a pair in `A1 ×_A A2` as an element of `kerModule f2`. -/
noncomputable def cospanPullbackKerDiff {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (z : (cospanPullback f1 f2 h hh).carrier) :
    kerModule f2 IsSmallExtension.ker_annihilated :=
  ⟨AlgHom.pullbackSnd f1.hom f2.hom z - h.hom (AlgHom.pullbackFst f1.hom f2.hom z), sorry⟩

/-- The kernel component of `g` lands in `ker f2`. -/
theorem cospanPullbackKerDiff_mem {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (z : (cospanPullback f1 f2 h hh).carrier) :
    (cospanPullbackKerDiff h hh z).1 ∈ RingHom.ker f2.hom.toRingHom := sorry

/-- The map `g : A1 ×_A A2 ⟶ k[I]` given by `g(u, v) = residue(u) ⊕ (v - h(u))`. -/
noncomputable def cospanPullbackDiff {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullback f1 f2 h hh ⟶ squareZero Λ k (kerModule f2 IsSmallExtension.ker_annihilated) where
  hom :=
    { toFun := fun z ↦
        (inl ((toResidue A1).hom (AlgHom.pullbackFst f1.hom f2.hom z)) :
            TrivSqZeroExt k (kerModule f2 IsSmallExtension.ker_annihilated)) +
          inr (cospanPullbackKerDiff h hh z)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- `cospanPullbackDiff` evaluates to `inl (toResidue u) + inr (v - h(u))`. -/
theorem cospanPullbackDiff_apply {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (z : (cospanPullback f1 f2 h hh).carrier) :
    (cospanPullbackDiff h hh).hom z =
      (inl ((toResidue A1).hom (AlgHom.pullbackFst f1.hom f2.hom z)) :
          TrivSqZeroExt k (kerModule f2 IsSmallExtension.ker_annihilated)) +
        inr (cospanPullbackKerDiff h hh z) := sorry

/-- The map `g` is a local residue-compatible algebra homomorphism with the stated formula. -/
theorem cospanPullbackDiff_spec {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (z : (cospanPullback f1 f2 h hh).carrier) :
    (cospanPullbackDiff h hh).hom z =
        (inl ((toResidue A1).hom (AlgHom.pullbackFst f1.hom f2.hom z)) :
            TrivSqZeroExt k (kerModule f2 IsSmallExtension.ker_annihilated)) +
          inr (cospanPullbackKerDiff h hh z) ∧
      IsLocalHom (cospanPullbackDiff h hh).hom ∧
      (squareZero Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).residueFieldIso.toAlgHom.comp
          (ResidueField.mapAlgHom (cospanPullbackDiff h hh).hom) =
        (cospanPullback f1 f2 h hh).residueFieldIso.toAlgHom := sorry

/-- The underlying algebra map of the comparison `(u, v) ↦ (u, g(u, v))`. -/
noncomputable def cospanPullbackIsoHom {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullback f1 f2 h hh ⟶
      squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated) where
  hom :=
    AlgHom.codRestrict
      (AlgHom.prod (cospanPullbackFst f1 f2 h hh).hom (cospanPullbackDiff h hh).hom)
      (AlgHom.pullback (toResidue A1).hom
        (squareZeroToResidue Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).hom)
      sorry
  isLocalHom := sorry
  residue_compat := sorry

/-- The inverse comparison `(a, residue ⊕ i) ↦ (a, h(a) + i)`. -/
noncomputable def cospanPullbackIsoInv {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated) ⟶
      cospanPullback f1 f2 h hh where
  hom :=
    { toFun := fun z ↦
        let a :=
          AlgHom.pullbackFst (toResidue A1).hom
            (squareZeroToResidue Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).hom z
        let t :=
          AlgHom.pullbackSnd (toResidue A1).hom
            (squareZeroToResidue Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).hom z
        ⟨(a, h.hom a + t.snd), sorry⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- The isomorphism `A1 ×_A A2 ≅ A1 ×_k k[I]` given by `(u, v) ↦ (u, g(u, v))`. -/
noncomputable def cospanPullbackIso {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullback f1 f2 h hh ≅
      squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated) where
  hom := cospanPullbackIsoHom h hh
  inv := cospanPullbackIsoInv h hh
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The comparison isomorphism commutes with first projections to `A1`. -/
theorem cospanPullbackIso_hom_fst {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackIso h hh).hom ≫
        squareZeroPullbackFst A1 (kerModule f2 IsSmallExtension.ker_annihilated) =
      cospanPullbackFst f1 f2 h hh := sorry

/-- The comparison isomorphism has second projection equal to `g`. -/
theorem cospanPullbackIso_hom_snd {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackIso h hh).hom ≫
        squareZeroPullbackSnd A1 (kerModule f2 IsSmallExtension.ker_annihilated) =
      cospanPullbackDiff h hh := sorry

end ArtinianLocalAlgCat
