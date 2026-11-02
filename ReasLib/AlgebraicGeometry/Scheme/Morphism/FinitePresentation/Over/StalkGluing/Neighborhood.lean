/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.Concrete
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Cancellation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Etale

/-!
# Properties of finite-presentation stalk gluing near a point

This file records that standard properties of the open and stalk components of finite-presentation
gluing data hold on a sufficiently small open neighborhood of the gluing point.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FinitePresentationOver.StalkGluing

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
separated, then the morphism is separated over some smaller open neighborhood containing the
fixed open. -/
theorem existsOpenNeighborhood_isSeparated_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsSeparated (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsSeparated (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsSeparated (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
proper, then the morphism is proper over some smaller open neighborhood containing the fixed
open. -/
theorem existsOpenNeighborhood_isProper_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsProper (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsProper (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsProper (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
finite, then the morphism is finite over some smaller open neighborhood containing the fixed
open. -/
theorem existsOpenNeighborhood_isFinite_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsFinite (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsFinite (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsFinite (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
étale, then the morphism is étale over some smaller open neighborhood containing the fixed open.
-/
theorem existsOpenNeighborhood_etale_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : Etale (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : Etale (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        Etale (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- Object properties are the corresponding properties of the morphism to the identity
object. The terminal objects and their pullback identifications below are canonical; no
existence theorem for gluing or for descent is used to construct them. -/
private theorem existsOpenNeighborhood_object_of_morphism
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (S : Scheme.{u}) (U U' : S.Opens) (s : S)
    (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (hmorphism : ∀ {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
      {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂),
      (∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
          (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
        FinitePresentationOver.restrictOverHom hUU' a =
          e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv) →
      (∃ (e₁ : FinitePresentationOver.baseChangeOverObject
            (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
          (e₂ : FinitePresentationOver.baseChangeOverObject
            (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
        FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
          e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
            e₂.inv) →
      P (FinitePresentationOver.underlyingHom α.fst) →
      P (FinitePresentationOver.underlyingHom α.snd) →
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧ P (FinitePresentationOver.restrictOverHom hWU' a).left)
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : P (Comma.hom G.fst.obj)) (hstalk : P (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧ P (FinitePresentationOver.restrictOverObject hWU' X').hom := by
  let T (B : Scheme.{u}) : FinitePresentationOver B :=
    ⟨Over.mk (𝟙 B), inferInstanceAs (Scheme.Hom.FinitePresentation (𝟙 B))⟩
  let e {B B' : Scheme.{u}} (f : B' ⟶ B) :
      FinitePresentationOver.baseChangeOverObject f (T B) ≅ (T B').obj := by
    let e' : pullback (𝟙 B) f ≅ B' :=
      { hom := pullback.snd (𝟙 B) f
        inv := pullback.lift f (𝟙 B') (by
          exact (Category.comp_id f).trans (Category.id_comp f).symm)
        hom_inv_id := by
          apply pullback.hom_ext
          · simpa only [Category.assoc, pullback.lift_fst, Category.id_comp,
              Category.comp_id] using (pullback.condition (f := 𝟙 B) (g := f)).symm
          · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
        inv_hom_id := pullback.lift_snd _ _ _ }
    exact Over.isoMk e' (by
      change pullback.snd (𝟙 B) f ≫ (𝟙 B') = pullback.snd (𝟙 B) f
      exact Category.comp_id _)
  let H : finitePresentationStalkGluingCategory S U s :=
    { fst := T U.toScheme
      snd := T (Spec (S.presheaf.stalk s))
      iso := (finitePresentationOverProperty (stalkOpenIntersection S U s).toScheme).isoMk
        (e ((S.fromSpecStalk s) ∣_ U) ≪≫ (e (stalkOpenIntersection S U s).ι).symm) }
  let a : X' ⟶ T U'.toScheme := ObjectProperty.homMk (Over.homMk X'.obj.hom)
  let α : G ⟶ H :=
    { fst := ObjectProperty.homMk (Over.homMk G.fst.obj.hom)
      snd := ObjectProperty.homMk (Over.homMk G.snd.obj.hom)
      w := by
        apply ObjectProperty.hom_ext
        exact (Over.mkIdTerminal.ofIso (e (stalkOpenIntersection S U s).ι).symm).hom_ext _ _ }
  obtain ⟨eOpen⟩ := hOpenIso
  obtain ⟨eStalk⟩ := hStalkIso
  have hOpenComm : ∃
      (e₁ : FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj)
      (e₂ : FinitePresentationOver.restrictOverObject hUU' (T U'.toScheme) ≅ H.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv := by
    refine ⟨eOpen, e (S.homOfLE hUU'), ?_⟩
    exact (Over.mkIdTerminal.ofIso (e (S.homOfLE hUU')).symm).hom_ext _ _
  have hStalkComm : ∃
      (e₁ : FinitePresentationOver.baseChangeOverObject
        (U'.fromSpecStalkOfMem s hsU') X' ≅ G.snd.obj)
      (e₂ : FinitePresentationOver.baseChangeOverObject
        (U'.fromSpecStalkOfMem s hsU') (T U'.toScheme) ≅ H.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv := by
    refine ⟨eStalk, e (U'.fromSpecStalkOfMem s hsU'), ?_⟩
    exact (Over.mkIdTerminal.ofIso (e (U'.fromSpecStalkOfMem s hsU')).symm).hom_ext _ _
  obtain ⟨W, hUW, hWU', hsW, hW⟩ := hmorphism a α hOpenComm hStalkComm hopen hstalk
  refine ⟨W, hUW, hWU', hsW, ?_⟩
  haveI : IsIso (FinitePresentationOver.restrictOverObject hWU' (T U'.toScheme)).hom := by
    change IsIso (e (S.homOfLE hWU')).hom.left
    infer_instance
  simpa only [Over.w] using
    (MorphismProperty.RespectsIso.postcomp P
      (FinitePresentationOver.restrictOverObject hWU' (T U'.toScheme)).hom
      (FinitePresentationOver.restrictOverHom hWU' a).left hW)

/-- If the open and stalk components of a finite-presentation gluing object are separated, then
the object is separated over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_isSeparated_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : IsSeparated (Comma.hom G.fst.obj))
    (hstalk : IsSeparated (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsSeparated (FinitePresentationOver.restrictOverObject hWU' X').hom := by
  exact existsOpenNeighborhood_object_of_morphism @IsSeparated S U U' s hUU' hsU'
    (existsOpenNeighborhood_isSeparated_of_morphism_components S U U' s hsU hUU' hsU')
    X' G hOpenIso hStalkIso hopen hstalk

/-- If the open and stalk components of a finite-presentation gluing object are proper, then
the object is proper over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_isProper_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : IsProper (Comma.hom G.fst.obj))
    (hstalk : IsProper (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsProper (FinitePresentationOver.restrictOverObject hWU' X').hom := by
  exact existsOpenNeighborhood_object_of_morphism @IsProper S U U' s hUU' hsU'
    (existsOpenNeighborhood_isProper_of_morphism_components S U U' s hsU hUU' hsU')
    X' G hOpenIso hStalkIso hopen hstalk

/-- If the open and stalk components of a finite-presentation gluing object are finite, then
the object is finite over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_isFinite_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : IsFinite (Comma.hom G.fst.obj))
    (hstalk : IsFinite (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsFinite (FinitePresentationOver.restrictOverObject hWU' X').hom := by
  exact existsOpenNeighborhood_object_of_morphism @IsFinite S U U' s hUU' hsU'
    (existsOpenNeighborhood_isFinite_of_morphism_components S U U' s hsU hUU' hsU')
    X' G hOpenIso hStalkIso hopen hstalk

/-- If the open and stalk components of a finite-presentation gluing object are étale, then
the object is étale over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_etale_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : Etale (Comma.hom G.fst.obj))
    (hstalk : Etale (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        Etale (FinitePresentationOver.restrictOverObject hWU' X').hom := by
  exact existsOpenNeighborhood_object_of_morphism @Etale S U U' s hUU' hsU'
    (existsOpenNeighborhood_etale_of_morphism_components S U U' s hsU hUU' hsU')
    X' G hOpenIso hStalkIso hopen hstalk

end AlgebraicGeometry.FinitePresentationOver.StalkGluing
