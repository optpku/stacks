/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Elements

/-!
# Set-valued Schlessinger conditions

For a set-valued functor on Artinian local algebras, the pullback comparison
maps give the set-theoretic forms of Schlessinger's conditions.
-/

@[expose] public section

open CategoryTheory Limits ArtinianLocalAlgCat Opposite

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The canonical comparison sends an element of a pullback to its two projected images. -/
def pullbackObjMap_subtype (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {P A A1 A2 : ArtinianLocalAlgCat Λ k}
    (π1 : P ⟶ A1) (π2 : P ⟶ A2) (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (h : IsPullback π1 π2 f1 f2) :
    F.obj P → Types.PullbackObj (F.map f1) (F.map f2) :=
  fun y ↦
    (PullbackCone.mk (F.map π1) (F.map π2) (F.map_commSq h.toCommSq).w).toPullbackObj y

/-- A functor satisfies the set-valued Schlessinger condition (H1) when every
surjective pullback comparison is surjective. -/
class HasSchlessingerH1 (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- The comparison map is surjective whenever the second cospan leg is surjective. -/
  surjective_pullbackObjMap :
    ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
      (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
      Function.Surjective f2.hom →
        Function.Surjective (pullbackObjMap_subtype F π1 π2 f1 f2 h)

/-- A functor satisfies the set-valued Schlessinger condition (H2) when every
dual-number pullback comparison is bijective. -/
class HasSchlessingerH2 (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- The dual-number comparison map is bijective. -/
  bijective_pullbackObjMap :
    ∀ {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
      (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
      (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)),
      Function.Bijective
        (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h)

/-- The set-valued Schlessinger condition (H1) is equivalent to surjectivity
onto every matching pair of values. -/
theorem hasSchlessingerH1_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerH1 F ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2),
        IsPullback π1 π2 f1 f2 →
          Function.Surjective f2.hom →
            ∀ (x1 : F.obj A1) (x2 : F.obj A2),
              F.map f1 x1 = F.map f2 x2 →
                ∃ y : F.obj P, F.map π1 y = x1 ∧ F.map π2 y = x2 := by
  constructor
  · intro hF A A1 A2 P f1 f2 π1 π2 h hs x1 x2 hx
    obtain ⟨y, hy⟩ := hF.surjective_pullbackObjMap f1 f2 π1 π2 h hs ⟨⟨x1, x2⟩, hx⟩
    exact ⟨y, congrArg (fun z ↦ z.val.1) hy, congrArg (fun z ↦ z.val.2) hy⟩
  · intro hF
    constructor
    intro A A1 A2 P f1 f2 π1 π2 h hs x
    obtain ⟨y, hy1, hy2⟩ := hF f1 f2 π1 π2 h hs x.val.1 x.val.2 x.property
    exact ⟨y, Subtype.ext (Prod.ext hy1 hy2)⟩

/-- The set-valued Schlessinger condition (H2) is equivalent to bijectivity
of every dual-number pullback comparison. -/
theorem hasSchlessingerH2_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerH2 F ↔
      ∀ {A P : ArtinianLocalAlgCat Λ k} (f : A ⟶ residue Λ k)
        (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
        (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)),
        Function.Bijective
          (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h) := by
  exact ⟨fun h ↦ h.bijective_pullbackObjMap, fun h ↦ ⟨h⟩⟩

/-- The coyoneda functor of an Artinian local algebra satisfies (H1). -/
instance instHasSchlessingerH1Coyoneda (A : ArtinianLocalAlgCat Λ k) :
    HasSchlessingerH1 (coyoneda.obj (op A)) := by
  apply (hasSchlessingerH1_iff _).mpr
  intro B A1 A2 P f1 f2 π1 π2 h _ x1 x2 hx
  exact h.exists_lift x1 x2 hx

/-- The coyoneda functor of an Artinian local algebra satisfies (H2). -/
instance instHasSchlessingerH2Coyoneda (A : ArtinianLocalAlgCat Λ k) :
    HasSchlessingerH2 (coyoneda.obj (op A)) := by
  constructor
  intro B P f π1 π2 h
  constructor
  · intro y1 y2 hy
    exact h.hom_ext (congrArg (fun z ↦ z.val.1) hy) (congrArg (fun z ↦ z.val.2) hy)
  · intro x
    obtain ⟨y, hy1, hy2⟩ := h.exists_lift x.val.1 x.val.2 x.property
    exact ⟨y, Subtype.ext (Prod.ext hy1 hy2)⟩

/-- Injectivity of the dual-number comparison is equivalent to uniqueness of
an element with prescribed images under both projections. -/
theorem pullbackObjMap_subtype_injective_iff_unique
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) {A P : ArtinianLocalAlgCat Λ k}
    (f : A ⟶ residue Λ k) (π1 : P ⟶ A) (π2 : P ⟶ dualNumber Λ k)
    (h : IsPullback π1 π2 f (dualNumberToResidue Λ k)) :
    Function.Injective (pullbackObjMap_subtype F π1 π2 f (dualNumberToResidue Λ k) h) ↔
      ∀ y₁ y₂ : F.obj P,
        F.map π1 y₁ = F.map π1 y₂ →
          F.map π2 y₁ = F.map π2 y₂ → y₁ = y₂ := by
  constructor
  · intro hi y1 y2 h1 h2
    exact hi (Subtype.ext (Prod.ext h1 h2))
  · intro hu y1 y2 hy
    exact hu y1 y2 (congrArg (fun z ↦ z.val.1) hy) (congrArg (fun z ↦ z.val.2) hy)

/-- The categorical condition (S1) for the category-of-elements projection is
equivalent to the set-valued condition (H1). -/
theorem hasSchlessingerS1_iff_hasSchlessingerH1
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerS1 (CategoryOfElements.π F) ↔ HasSchlessingerH1 F := by
  constructor
  · intro hF
    apply (hasSchlessingerH1_iff F).mpr
    intro A A1 A2 P f1 f2 π1 π2 h hs x1 x2 hx
    let d : F.elementsMk A1 x1 ⟶ F.elementsMk A (F.map f1 x1) := ⟨f1, rfl⟩
    let e : F.elementsMk A2 x2 ⟶ F.elementsMk A (F.map f1 x1) := ⟨f2, hx.symm⟩
    obtain ⟨y, a, c, hsq, _⟩ := hF.exists_completion d e hs
    let l := h.lift a.val c.val (congrArg Subtype.val hsq.w)
    refine ⟨F.map l y.snd, ?_, ?_⟩
    · rw [← F.map_comp_apply, IsPullback.lift_fst]
      exact a.property
    · rw [← F.map_comp_apply, IsPullback.lift_snd]
      exact c.property
  · intro hF
    refine { isCofiberedInGroupoids := inferInstance, exists_completion := ?_ }
    intro x x1 x2 d e hs
    obtain ⟨P, π1, π2, _, hP⟩ :=
      (inferInstance : HasSchlessingerS1 (𝟭 (ArtinianLocalAlgCat Λ k))).exists_completion
        d.val e.val hs
    obtain ⟨y, hy1, hy2⟩ := (hasSchlessingerH1_iff F).mp hF
      d.val e.val π1 π2 hP hs x1.snd x2.snd (d.property.trans e.property.symm)
    refine ⟨⟨P, y⟩, ⟨π1, hy1⟩, ⟨π2, hy2⟩, ⟨?_, hP⟩⟩
    exact ⟨Subtype.ext hP.w⟩

/-- The categorical condition (S2) for the category-of-elements projection is
equivalent to the set-valued condition (H2). -/
theorem hasSchlessingerS2_iff_hasSchlessingerH2
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerS2 (CategoryOfElements.π F) ↔ HasSchlessingerH2 F := by
  constructor
  · intro hF
    constructor
    intro A P f π1 π2 h
    constructor
    · intro y1 y2 hy
      let x : F.Elements := ⟨A, F.map π1 y1⟩
      let x0 : F.Elements := ⟨residue Λ k, F.map f (F.map π1 y1)⟩
      let xε : F.Elements := ⟨dualNumber Λ k, F.map π2 y1⟩
      let d : x ⟶ x0 := ⟨f, rfl⟩
      let e : xε ⟶ x0 := ⟨dualNumberToResidue Λ k, by
        dsimp [xε, x0]
        rw [← F.map_comp_apply, ← F.map_comp_apply, h.w]⟩
      let a : F.elementsMk P y1 ⟶ x := ⟨π1, rfl⟩
      let c : F.elementsMk P y1 ⟶ xε := ⟨π2, rfl⟩
      let a' : F.elementsMk P y2 ⟶ x :=
        ⟨π1, (congrArg (fun z ↦ z.val.1) hy).symm⟩
      let c' : F.elementsMk P y2 ⟶ xε :=
        ⟨π2, (congrArg (fun z ↦ z.val.2) hy).symm⟩
      obtain ⟨b, hb, _⟩ := hF.exists_vertical d e a c a' c' (.map e)
        ⟨Subtype.ext h.w⟩ ⟨Subtype.ext h.w⟩ h rfl (.map a') (.map c')
      haveI := hb
      have hbval : 𝟙 P = b.val :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ (CategoryOfElements.π F)
          (F.elementsMk P y1) (F.elementsMk P y2) (𝟙 P) b hb
      have hbpoint := b.property
      change F.map b.val y1 = y2 at hbpoint
      rw [← hbval, F.map_id_apply] at hbpoint
      exact hbpoint
    · intro x
      let d : F.elementsMk A x.val.1 ⟶ F.elementsMk (residue Λ k) (F.map f x.val.1) :=
        ⟨f, rfl⟩
      let e : F.elementsMk (dualNumber Λ k) x.val.2 ⟶
          F.elementsMk (residue Λ k) (F.map f x.val.1) :=
        ⟨dualNumberToResidue Λ k, x.property.symm⟩
      obtain ⟨y, a, c, hsq, _⟩ := hF.exists_completion d e (.map e)
      let l := h.lift a.val c.val (congrArg Subtype.val hsq.w)
      refine ⟨F.map l y.snd, Subtype.ext (Prod.ext ?_ ?_)⟩
      · change F.map π1 (F.map l y.snd) = x.val.1
        rw [← F.map_comp_apply, IsPullback.lift_fst]
        exact a.property
      · change F.map π2 (F.map l y.snd) = x.val.2
        rw [← F.map_comp_apply, IsPullback.lift_snd]
        exact c.property
  · intro hF
    refine
      { isCofiberedInGroupoids := inferInstance
        exists_completion := ?_
        exists_vertical := ?_ }
    · intro x x0 xε d e he
      haveI := he
      rcases x0 with ⟨B, x0⟩
      rcases xε with ⟨E, xε⟩
      have hB : B = residue Λ k :=
        IsHomLift.codomain_eq (CategoryOfElements.π F) (dualNumberToResidue Λ k) e
      have hE : E = dualNumber Λ k :=
        IsHomLift.domain_eq (CategoryOfElements.π F) (dualNumberToResidue Λ k) e
      subst B E
      have heq : e.val = dualNumberToResidue Λ k :=
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (CategoryOfElements.π F)
          (F.elementsMk (dualNumber Λ k) xε) (F.elementsMk (residue Λ k) x0)
          (dualNumberToResidue Λ k) e he).symm
      obtain ⟨P, π1, π2, _, hP⟩ :=
        (inferInstance : HasSchlessingerS1 (𝟭 (ArtinianLocalAlgCat Λ k))).exists_completion
          d.val (dualNumberToResidue Λ k) (dualNumberToResidue_surjective Λ k)
      have hx : F.map d.val x.snd = F.map (dualNumberToResidue Λ k) xε := by
        rw [← heq]
        exact d.property.trans e.property.symm
      obtain ⟨y, hy⟩ := (hF.bijective_pullbackObjMap d.val π1 π2 hP).surjective
        ⟨⟨x.snd, xε⟩, hx⟩
      refine ⟨⟨P, y⟩, ⟨π1, congrArg (fun z ↦ z.val.1) hy⟩,
        ⟨π2, congrArg (fun z ↦ z.val.2) hy⟩, ?_, ?_⟩
      · refine ⟨Subtype.ext ?_⟩
        change π1 ≫ d.val = π2 ≫ e.val
        rw [heq]
        exact hP.w
      · change IsPullback π1 π2 d.val e.val
        rw [heq]
        exact hP
    · intro x x0 xε y y' d e a c a' c' he _ _ hP hyy ha hc
      haveI := he
      rcases x0 with ⟨B, x0⟩
      rcases xε with ⟨E, xε⟩
      have hB : B = residue Λ k :=
        IsHomLift.codomain_eq (CategoryOfElements.π F) (dualNumberToResidue Λ k) e
      have hE : E = dualNumber Λ k :=
        IsHomLift.domain_eq (CategoryOfElements.π F) (dualNumberToResidue Λ k) e
      subst B E
      have heq : e.val = dualNumberToResidue Λ k :=
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (CategoryOfElements.π F)
          (F.elementsMk (dualNumber Λ k) xε) (F.elementsMk (residue Λ k) x0)
          (dualNumberToResidue Λ k) e he).symm
      rcases y with ⟨Y, y⟩
      rcases y' with ⟨Y', y'⟩
      change Y = Y' at hyy
      subst Y'
      have haeq : a.val = a'.val :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ (CategoryOfElements.π F)
          (F.elementsMk Y y') x a.val a' ha
      have hceq : c.val = c'.val :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ (CategoryOfElements.π F)
          (F.elementsMk Y y') (F.elementsMk (dualNumber Λ k) xε) c.val c' hc
      have hP' : IsPullback a.val c.val d.val (dualNumberToResidue Λ k) := by
        change IsPullback a.val c.val d.val e.val at hP
        simpa only [heq] using hP
      have hy : y = y' := by
        apply (hF.bijective_pullbackObjMap d.val a.val c.val hP').injective
        apply Subtype.ext
        apply Prod.ext
        · change F.map a.val y = F.map a.val y'
          exact a.property.trans (by rw [haeq]; exact a'.property.symm)
        · change F.map c.val y = F.map c.val y'
          exact c.property.trans (by rw [hceq]; exact c'.property.symm)
      let b : F.elementsMk Y y ⟶ F.elementsMk Y y' :=
        ⟨𝟙 Y, (F.map_id_apply Y y).trans hy⟩
      refine ⟨b, .map b, Subtype.ext ?_⟩
      change 𝟙 Y ≫ a'.val = a.val
      simpa only [Category.id_comp] using haeq.symm

end CategoryTheory.Functor
