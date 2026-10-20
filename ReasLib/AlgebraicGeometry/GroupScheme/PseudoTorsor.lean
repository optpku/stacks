/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

@[expose] public section

open CategoryTheory
open scoped MonObj ModObj

universe u

namespace AlgebraicGeometry.GroupScheme

open CategoryTheory.Mod

variable (S : Scheme.{u}) (G : Grp (Over S)) (X : Mod (Over S) G.X)

/-- A pseudo-torsor under a group scheme is trivial exactly when its structure
morphism is a split epimorphism. -/
theorem isTrivial_iff_isSplitEpi [IsPseudoTorsor X] :
    X.IsTrivial ↔ IsSplitEpi X.X.hom := by
  constructor
  · intro hX
    rcases hX with ⟨e⟩
    -- Transport the unit section of the regular torsor across the chosen trivialization.
    refine IsSplitEpi.mk' ?_
    refine
      { section_ := (η[G.X] ≫ e.hom.hom).left
        id := ?_ }
    simpa using Over.w (η[G.X] ≫ e.hom.hom)
  · intro hsplit
    let s : S ⟶ X.X.left := section_ X.X.hom
    have hs : s ≫ X.X.hom = 𝟙 S := IsSplitEpi.id X.X.hom
    -- Local instance justification (proof-local temporary data): install the regular action only for the temporary comparison construction in this proof.
    letI : ModObj G.X G.X := ModObj.regular G.X
    let xPoint : ∀ T : Over S, T ⟶ X.X := fun T ↦
      Over.homMk (T.hom ≫ s) (by simpa [Category.assoc, hs])
    let u : G.X ⟶ X.X :=
      CartesianMonoidalCategory.lift (𝟙 G.X) (xPoint G.X) ≫ γ[G.X, X.X]
    have hxPoint_comp : ∀ ⦃T : Over S⦄ (g : T ⟶ G.X), g ≫ xPoint G.X = xPoint T := by
      intro T g
      ext
      simpa [xPoint, Category.assoc] using congrArg (fun k ↦ k ≫ s) (Over.w g)
    have htranslate : ∀ (T : Over S) (g : T ⟶ G.X), g ≫ u = g • xPoint T := by
      -- Normalize postcomposition with the translation map for Yoneda bijectivity.
      intro T g
      calc
        g ≫ u = g ≫ CartesianMonoidalCategory.lift (𝟙 G.X) (xPoint G.X) ≫ γ[G.X, X.X] := by
          rfl
        _ = (g ≫ CartesianMonoidalCategory.lift (𝟙 G.X) (xPoint G.X)) ≫ γ[G.X, X.X] := by
          rw [Category.assoc]
        _ = CartesianMonoidalCategory.lift (g ≫ 𝟙 G.X) (g ≫ xPoint G.X) ≫ γ[G.X, X.X] := by
          rw [CartesianMonoidalCategory.comp_lift]
        _ = CartesianMonoidalCategory.lift g (xPoint T) ≫ γ[G.X, X.X] := by
          rw [hxPoint_comp g]
          simp
        _ = g • xPoint T := by
          rw [Hom.smul_def]
    have hsimple :
        ∀ (T : Over S) (x y : T ⟶ X.X), ∃! g : T ⟶ G.X, g • x = y :=
      (isPseudoTorsor_iff_forall_existsUnique_smul X).1 inferInstance
    have huIso : IsIso u := by
      -- The pseudo-torsor axiom gives pointwise simple transitivity, hence Yoneda bijectivity.
      refine isIso_of_yoneda_map_bijective u ?_
      intro T
      rw [Function.bijective_iff_existsUnique]
      intro y
      rcases hsimple T (xPoint T) y with ⟨g, hg, huniq⟩
      refine ⟨g, ?_, ?_⟩
      · exact (htranslate T g).trans hg
      · intro g' hg'
        exact huniq g' ((htranslate T g').symm.trans hg')
    -- Local instance justification (proof-local temporary data): install the derived isomorphism fact only for temporary categorical inverse and cancellation API.
    letI : IsIso u := huIso
    let e₀ : G.X ≅ X.X := asIso u
    have huLinear : IsModHom G.X u := by
      -- The translation map is left multiplication by the chosen section, hence equivariant.
      let P : Over S := MonoidalCategoryStruct.tensorObj G.X G.X
      have hwhisker :
          CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst G.X G.X)
              (CartesianMonoidalCategory.snd G.X G.X ≫ u) =
            MonoidalCategory.MonoidalLeftActionStruct.actionHomRight G.X u := by
        simpa [CartesianMonoidalCategory.lift_fst_snd] using
          (CartesianMonoidalCategory.lift_whiskerLeft
            (f := CartesianMonoidalCategory.fst G.X G.X)
            (g := CartesianMonoidalCategory.snd G.X G.X) (h := u)).symm
      have hμ :
          γ[G.X, G.X] ≫ u = μ[G.X] • xPoint P := by
        simpa [P] using htranslate P μ[G.X]
      have hmul :
          μ[G.X] • xPoint P =
            (CartesianMonoidalCategory.fst G.X G.X) •
              ((CartesianMonoidalCategory.snd G.X G.X) • xPoint P) := by
        simpa [Hom.mul_def, CartesianMonoidalCategory.lift_fst_snd] using
          (mul_smul (CartesianMonoidalCategory.fst G.X G.X)
            (CartesianMonoidalCategory.snd G.X G.X) (xPoint P))
      have hsnd :
          (CartesianMonoidalCategory.fst G.X G.X) •
              ((CartesianMonoidalCategory.snd G.X G.X) • xPoint P) =
            (CartesianMonoidalCategory.fst G.X G.X) •
              (CartesianMonoidalCategory.snd G.X G.X ≫ u) := by
        rw [htranslate P (CartesianMonoidalCategory.snd G.X G.X)]
      have hsmul :
          (CartesianMonoidalCategory.fst G.X G.X) •
              (CartesianMonoidalCategory.snd G.X G.X ≫ u) =
            CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst G.X G.X)
              (CartesianMonoidalCategory.snd G.X G.X ≫ u) ≫ γ[G.X, X.X] := by
        rw [Hom.smul_def]
      refine ⟨?_⟩
      exact hμ.trans <| hmul.trans <| hsnd.trans <| hsmul.trans <| by rw [hwhisker]
    have htrivial : X.IsTrivial := by
      -- Package the underlying isomorphism together with the equivariance of the translation.
      let e : G.X ≅ X.X := asIso u
      -- Local instance justification (proof-local temporary data): install the derived equivariance of `u` only while constructing the bundled module isomorphism.
      letI : IsModHom G.X u := huLinear
      have hHomLinear : IsModHom G.X e.hom := by
        simpa [e] using huLinear
      have hInvLinear : IsModHom G.X e.inv := by
        -- Local instance justification (proof-local temporary data): install the derived equivariance of `e.hom` only to infer equivariance of the temporary inverse.
        letI : IsModHom G.X e.hom := hHomLinear
        infer_instance
      refine ⟨{ hom := Mod.Hom.mk' u huLinear.smul_hom
              , inv := Mod.Hom.mk' e.inv hInvLinear.smul_hom
              , hom_inv_id := ?_
              , inv_hom_id := ?_ }⟩
      · apply Mod.hom_ext
        exact e.hom_inv_id
      · apply Mod.hom_ext
        exact e.inv_hom_id
    exact htrivial

/-- A pseudo-torsor under a group scheme is trivial exactly when its structure
morphism admits a section. -/
theorem isTrivial_iff_exists_section [IsPseudoTorsor X] :
    X.IsTrivial ↔ ∃ s : S ⟶ X.X.left, s ≫ X.X.hom = 𝟙 S := by
  rw [isTrivial_iff_isSplitEpi]
  constructor
  · intro hX
    exact ⟨section_ X.X.hom, IsSplitEpi.id X.X.hom⟩
  · rintro ⟨s, hs⟩
    exact IsSplitEpi.mk' { section_ := s, id := hs }

end AlgebraicGeometry.GroupScheme
