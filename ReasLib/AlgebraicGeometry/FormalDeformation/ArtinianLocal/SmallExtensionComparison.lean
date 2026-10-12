/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.CospanPullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Kernel
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroPullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension

/-!
# Comparison of a cospan pullback with a square-zero pullback

For a small extension, the difference of the second coordinate and a chosen
lift factors through the annihilated kernel. This gives an explicit comparison
with the corresponding trivial square-zero pullback.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A1 A2 : ArtinianLocalAlgCat Λ k}

/-- The difference of the coordinates is a kernel element. -/
noncomputable def cospanPullbackKerDiff {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (z : (cospanPullback f1 f2 h hh).carrier) :
    kerModule f2 IsSmallExtension.ker_annihilated :=
  ⟨AlgHom.pullbackSnd f1.hom f2.hom z - h.hom (AlgHom.pullbackFst f1.hom f2.hom z), sorry⟩

/-- The difference coordinate of a cospan pullback lies in the small-extension kernel. -/
theorem cospanPullback_sub_mem_ker {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (z : (cospanPullback f1 f2 h hh).carrier) :
    (cospanPullbackKerDiff h hh z).1 ∈ RingHom.ker f2.hom.toRingHom := sorry

/-- The difference map on the underlying pullback algebra. -/
noncomputable def cospanPullbackDiffHom {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullback f1 f2 h hh).carrier →ₐ[Λ]
      (squareZero Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).carrier :=
  { toFun := fun z ↦
      (inl ((toResidue A1).hom (AlgHom.pullbackFst f1.hom f2.hom z)) :
          TrivSqZeroExt k (kerModule f2 IsSmallExtension.ker_annihilated)) +
        inr (cospanPullbackKerDiff h hh z)
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry
    commutes' := sorry }

/-- The local, residue-compatible difference morphism. -/
noncomputable def cospanPullbackDiff {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullback f1 f2 h hh ⟶ squareZero Λ k (kerModule f2 IsSmallExtension.ker_annihilated) :=
  Hom.of (cospanPullbackDiffHom h hh) sorry sorry

/-- The difference morphism has the explicit residue-plus-kernel formula. -/
theorem cospanPullbackDiff_apply {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) (z : (cospanPullback f1 f2 h hh).carrier) :
    (cospanPullbackDiff h hh).hom z =
      (inl ((toResidue A1).hom (AlgHom.pullbackFst f1.hom f2.hom z)) :
          TrivSqZeroExt k (kerModule f2 IsSmallExtension.ker_annihilated)) +
        inr (cospanPullbackKerDiff h hh z) := rfl

/-- The forward comparison has the prescribed pullback target. -/
noncomputable def cospanPullbackIsoHomAlgHom {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullback f1 f2 h hh).carrier →ₐ[Λ]
      (squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated)).carrier :=
  AlgHom.codRestrict
    (AlgHom.prod (cospanPullbackFst f1 f2 h hh).hom (cospanPullbackDiff h hh).hom)
    (AlgHom.pullback (toResidue A1).hom
      (squareZeroToResidue Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).hom)
    sorry

/-- The forward comparison is a local residue-compatible morphism. -/
noncomputable def cospanPullbackIsoHom {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullback f1 f2 h hh ⟶
      squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated) :=
  Hom.of (cospanPullbackIsoHomAlgHom h hh) sorry sorry

/-- The inverse comparison has the prescribed formula. -/
noncomputable def cospanPullbackIsoInvAlgHom {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated)).carrier →ₐ[Λ]
      (cospanPullback f1 f2 h hh).carrier :=
  { toFun := fun z ↦
      let a := AlgHom.pullbackFst (toResidue A1).hom
        (squareZeroToResidue Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).hom z
      let t := AlgHom.pullbackSnd (toResidue A1).hom
        (squareZeroToResidue Λ k (kerModule f2 IsSmallExtension.ker_annihilated)).hom z
      ⟨(a, h.hom a + t.snd), sorry⟩
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry
    commutes' := sorry }

/-- The inverse comparison is a local residue-compatible morphism. -/
noncomputable def cospanPullbackIsoInv {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated) ⟶
      cospanPullback f1 f2 h hh :=
  Hom.of (cospanPullbackIsoInvAlgHom h hh) sorry sorry

/-- The comparison isomorphism is defined by the explicit forward and inverse maps. -/
noncomputable def cospanPullbackIso {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    cospanPullback f1 f2 h hh ≅
      squareZeroPullback A1 (kerModule f2 IsSmallExtension.ker_annihilated) where
  hom := cospanPullbackIsoHom h hh
  inv := cospanPullbackIsoInv h hh
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward comparison followed by its inverse is the identity. -/
theorem cospanPullbackIso_hom_inv_id {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackIso h hh).hom ≫ (cospanPullbackIso h hh).inv = 𝟙 _ := sorry

/-- The inverse followed by the forward comparison is the identity. -/
theorem cospanPullbackIso_inv_hom_id {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackIso h hh).inv ≫ (cospanPullbackIso h hh).hom = 𝟙 _ := sorry

/-- The forward comparison commutes with the first projection. -/
theorem cospanPullbackIso_hom_fst {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackIso h hh).hom ≫
        squareZeroPullbackFst A1 (kerModule f2 IsSmallExtension.ker_annihilated) =
    cospanPullbackFst f1 f2 h hh := sorry

/-- The forward comparison sends the second projection to the difference map. -/
theorem cospanPullbackIso_hom_snd {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
    [IsSmallExtension f2] (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) :
    (cospanPullbackIso h hh).hom ≫
        squareZeroPullbackSnd A1 (kerModule f2 IsSmallExtension.ker_annihilated) =
      cospanPullbackDiff h hh := sorry

end ArtinianLocalAlgCat
