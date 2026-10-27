/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Object
public import Mathlib.CategoryTheory.Adjunction.Basic

open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

private theorem trivialCrystalline_isDPMorphism_to_bot {Y Z : Scheme.{u}}
    (J : Z.IdealSheafData) (δ : ∀ V : Z.affineOpens, DividedPowers (J.ideal V))
    (f : Y ⟶ Z) (hJ : J ≤ f.ker) (V : Z.affineOpens) (W : Y.affineOpens)
    (hVW : W.1 ≤ f ⁻¹ᵁ V.1) :
    (δ V).IsDPMorphism (dividedPowersBot _) (f.appLE V W hVW).hom := by
  have hzero (a : Γ(Z, V)) (ha : a ∈ J.ideal V) :
      (f.appLE V W hVW).hom a = 0 := by
    have ha' := RingHom.mem_ker.mp (f.ideal_ker_le V (hJ V ha))
    simpa only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, map_zero]
      using congrArg (Y.presheaf.map (homOfLE hVW).op).hom ha'
  apply (DividedPowers.isDPMorphism_iff _ _ _).2
  refine ⟨?_, ?_⟩
  · change (J.ideal V).map (f.appLE V W hVW).hom ≤ ⊥
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact Ideal.mem_bot.mpr (hzero a ha)
  · intro n hn a ha
    rw [hzero a ha, (dividedPowersBot _).dpow_eval_zero hn,
      hzero _ ((δ V).dpow_mem hn ha)]

private theorem trivialCrystalline_hom_ext {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {A B : CrystallineObject S I γ h_compatible X x₀}
    (f g : CrystallineObject.Hom A B) (hs : f.source = g.source)
    (ht : f.thickening = g.thickening) : f = g := by
  cases f
  cases g
  cases hs
  cases ht
  rfl

/-- A morphism of trivial crystalline objects is induced by the same morphism on the source and
its underlying scheme map on the identity thickenings. -/
def trivialCrystallineObjectHom {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) {U V : Over X} (φ : U ⟶ V) :
    CrystallineObject.Hom
      (trivialCrystallineObject I γ h_compatible X x₀ U)
      (trivialCrystallineObject I γ h_compatible X x₀ V) where
  source := φ
  thickening := φ.left
  source_comm := (Category.comp_id φ.left).trans (Category.id_comp φ.left).symm
  base_comm := by
    change φ.left ≫ (V.hom ≫ x₀ ≫ I.subschemeι) = U.hom ≫ x₀ ≫ I.subschemeι
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ x₀ ≫ I.subschemeι) (Over.w φ)
  ideal_compatible := (Scheme.IdealSheafData.comap_bot φ.left).le
  dividedPowers_compatible := by
    intro V W hVW
    exact trivialCrystalline_isDPMorphism_to_bot ⊥ (fun _ ↦ dividedPowersBot _)
      φ.left bot_le V W hVW

/-- The trivial crystalline functor sends a scheme over `X` to its identity thickening
with zero ideal and trivial divided powers, compatible with the fixed base divided powers. -/
noncomputable def crystallineTrivialFunctor (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    Over X ⥤ RelativeCRIS S I γ h_compatible X x₀ where
  obj := fun U ↦
    ⟨trivialCrystallineObject I γ h_compatible X x₀ U, by
      intro V W hVW
      apply trivialCrystalline_isDPMorphism_to_bot I γ
        (U.hom ≫ x₀ ≫ I.subschemeι) _ V W hVW
      simpa only [Category.assoc, I.ker_subschemeι] using
        (U.hom ≫ x₀).le_ker_comp I.subschemeι⟩
  map := fun {U V} φ ↦ trivialCrystallineObjectHom I γ h_compatible X x₀ φ
  map_id := by intro U; rfl
  map_comp := by intro U V W φ ψ; rfl

/-- The trivial functor is a one-sided inverse of the forgetful functor, expressed
as a natural isomorphism rather than a definitional equality of functors. -/
theorem crystallineTrivialFunctor_oneSidedInverse (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    Nonempty ((crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p) ⋙
      crystallineForgetful S I γ h_compatible s X x₀ h_p ≅ 𝟭 (Over X)) := by
  refine ⟨NatIso.ofComponents (fun U ↦ Iso.refl U) ?_⟩
  intro U V φ
  change φ ≫ 𝟙 V = 𝟙 U ≫ φ
  exact (Category.comp_id φ).trans (Category.id_comp φ).symm

/-- The trivial functor is left adjoint to the specified crystalline forgetful
functor. -/
theorem crystallineTrivialFunctor_leftAdjoint (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    Nonempty (crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p ⊣
      crystallineForgetful S I γ h_compatible s X x₀ h_p) := by
  refine ⟨Adjunction.mkOfHomEquiv
    { homEquiv := fun U T ↦
        { toFun := fun f ↦ f.source
          invFun := fun f ↦
            { source := f
              thickening := f.left ≫ T.1.inclusion
              source_comm := (Category.id_comp _).symm
              base_comm := by
                change (f.left ≫ T.1.inclusion) ≫ T.1.thickeningToBase =
                  U.hom ≫ x₀ ≫ I.subschemeι
                calc
                  (f.left ≫ T.1.inclusion) ≫ T.1.thickeningToBase =
                      f.left ≫ (T.1.inclusion ≫ T.1.thickeningToBase) :=
                    Category.assoc _ _ _
                  _ = f.left ≫ (T.1.source.hom ≫ x₀ ≫ I.subschemeι) :=
                    congrArg (fun g ↦ f.left ≫ g) T.1.source_comm
                  _ = (f.left ≫ T.1.source.hom) ≫ x₀ ≫ I.subschemeι :=
                    (Category.assoc _ _ _).symm
                  _ = U.hom ≫ x₀ ≫ I.subschemeι :=
                    congrArg (fun g ↦ g ≫ x₀ ≫ I.subschemeι) (Over.w f)
              ideal_compatible := by
                change T.1.ideal.comap (f.left ≫ T.1.inclusion) ≤ ⊥
                apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
                rw [Scheme.IdealSheafData.map_bot, T.1.ideal_eq_ker]
                exact f.left.le_ker_comp T.1.inclusion
              dividedPowers_compatible := by
                intro V W hVW
                apply trivialCrystalline_isDPMorphism_to_bot T.1.ideal T.1.gamma
                  (f.left ≫ T.1.inclusion) _ V W hVW
                rw [T.1.ideal_eq_ker]
                exact f.left.le_ker_comp T.1.inclusion }
          left_inv := fun f ↦ by
            apply trivialCrystalline_hom_ext
            · change f.source = f.source
              rfl
            · change f.source.left ≫ T.1.inclusion = f.thickening
              exact f.source_comm.trans (Category.id_comp f.thickening)
          right_inv := fun f ↦ rfl }
      homEquiv_naturality_left_symm := by
        intro U' U T f g
        apply trivialCrystalline_hom_ext
        · change f ≫ g = f ≫ g
          rfl
        · change (f ≫ g).left ≫ T.1.inclusion = f.left ≫ (g.left ≫ T.1.inclusion)
          simp only [Over.comp_left, Category.assoc]
      homEquiv_naturality_right := by
        intro U T T' f g
        rfl }⟩

/-- The object map of the crystalline trivial functor is the explicit identity thickening. -/
lemma crystallineTrivialFunctor_obj (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) (U : Over X) :
    ((crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj U).1 =
      trivialCrystallineObject I γ h_compatible X x₀ U := rfl

/-- The morphism map of the crystalline trivial functor is induced by the underlying map of an
arrow in `Over X`. -/
lemma crystallineTrivialFunctor_map (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    {U V : Over X} (φ : U ⟶ V) :
    (crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).map φ =
      trivialCrystallineObjectHom I γ h_compatible X x₀ φ := rfl

/-- Every object in the image of the crystalline trivial functor is compatible with the fixed
divided-power structure on the base. -/
lemma crystallineTrivialFunctor_isCrystalline (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) (U : Over X) :
    CrystallineBaseCompatible I γ h_compatible x₀
      ((crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj U).1 :=
  ((crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj U).2

end
