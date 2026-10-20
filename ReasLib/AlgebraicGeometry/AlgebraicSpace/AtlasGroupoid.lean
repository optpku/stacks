/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AtlasCoequalizer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Composition

/-! # The represented kernel-pair groupoid of an étale atlas -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- The representable étale presheaf property of an étale morphism from a scheme to an
algebraic space. -/
theorem atlasEtale (φ : ofOver U ⟶ X) [Etale φ] :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ := by
  have hid : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
      (𝟙 (yoneda.obj U)) := by
    change (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale) (Over.forget S)).presheaf
      (𝟙 (yoneda.obj U))
    exact MorphismProperty.id_mem _ _
  have h := Etale.of_etale (f := φ) (𝟙 (yoneda.obj U)) hid
  change (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
    (𝟙 (yoneda.obj U) ≫ φ) at h
  simpa only [ofOver, ofFunctor, AlgebraicSpace.functorOfPoints,
    CategoryTheory.Category.id_comp] using h

/-- The kernel-pair pre-relation `R = U ×_X U` of an étale atlas `φ : U ⟶ X`. -/
def atlasRelation (φ : ofOver U ⟶ X) [Etale φ] : Scheme.PreRelation U :=
  kernelPair φ (atlasEtale φ).rep

/-- `atlasRelation φ` is the represented kernel pair of `φ`. -/
theorem atlasRelation_eq (φ : ofOver U ⟶ X) [Etale φ] :
    atlasRelation φ = kernelPair φ (atlasEtale φ).rep :=
  rfl

/-- The kernel pair of an étale atlas is an internal equivalence relation. -/
instance isEquivalenceRelation_atlasRelation (φ : ofOver U ⟶ X) [Etale φ] :
    IsEquivalenceRelation (atlasRelation φ).t (atlasRelation φ).s :=
  isEquivalenceRelation φ (atlasEtale φ)

/-- The represented kernel pair, with its composition, diagonal and swap maps, satisfies
the source, target, identity, inverse and associativity laws of a groupoid scheme. -/
theorem atlasGroupoid_laws (φ : ofOver U ⟶ X) [Etale φ] :
  let r := atlasRelation φ
  let s := r.s
  let t := r.t
  let c := r.composition
  let e := (atlasEtale φ).rep.lift' (𝟙 U) (𝟙 U) rfl
  let i := (atlasEtale φ).rep.lift' ((atlasEtale φ).rep.snd φ)
    ((atlasEtale φ).rep.fst' φ) ((atlasEtale φ).rep.isPullback' φ).w.symm
  (c ≫ s = pullback.snd s t ≫ s) ∧
  (c ≫ t = pullback.fst s t ≫ t) ∧
  (e ≫ s = 𝟙 U) ∧
  (e ≫ t = 𝟙 U) ∧
  (i ≫ s = t) ∧
  (i ≫ t = s) ∧
  (∀ {T : Over S} (a b d : T ⟶ r.left)
      (h_ab : a ≫ s = b ≫ t) (h_bd : b ≫ s = d ≫ t)
      (h_ab_d : (pullback.lift a b h_ab ≫ c) ≫ s = d ≫ t)
      (h_a_bd : a ≫ s = (pullback.lift b d h_bd ≫ c) ≫ t),
      pullback.lift (pullback.lift a b h_ab ≫ c) d h_ab_d ≫ c =
        pullback.lift a (pullback.lift b d h_bd ≫ c) h_a_bd ≫ c) ∧
  (∀ {T : Over S} (a : T ⟶ r.left)
      (h : a ≫ s = ((a ≫ s) ≫ e) ≫ t),
      pullback.lift a ((a ≫ s) ≫ e) h ≫ c = a) ∧
  (∀ {T : Over S} (a : T ⟶ r.left)
      (h : ((a ≫ t) ≫ e) ≫ s = a ≫ t),
      pullback.lift ((a ≫ t) ≫ e) a h ≫ c = a) ∧
  (∀ {T : Over S} (a : T ⟶ r.left)
      (h : a ≫ s = (a ≫ i) ≫ t),
      pullback.lift a (a ≫ i) h ≫ c = (a ≫ t) ≫ e) ∧
  (∀ {T : Over S} (a : T ⟶ r.left)
      (h : (a ≫ i) ≫ s = a ≫ t),
      pullback.lift (a ≫ i) a h ≫ c = (a ≫ s) ≫ e) := by
  sorry

/-- The étale groupoid scheme `(U, R, s, t, c)` associated to an étale atlas `φ : U ⟶ X`. -/
def atlasGroupoid (φ : ofOver U ⟶ X) [Etale φ] : GroupoidScheme S where
  U := U
  R := (atlasRelation φ).left
  s := (atlasRelation φ).s
  t := (atlasRelation φ).t
  c := (atlasRelation φ).composition
  e := (atlasEtale φ).rep.lift' (𝟙 U) (𝟙 U) rfl
  i :=
    (atlasEtale φ).rep.lift' ((atlasEtale φ).rep.snd φ) ((atlasEtale φ).rep.fst' φ)
      ((atlasEtale φ).rep.isPullback' φ).w.symm
  comp_source := (atlasGroupoid_laws φ).1
  comp_target := (atlasGroupoid_laws φ).2.1
  identity_source := (atlasGroupoid_laws φ).2.2.1
  identity_target := (atlasGroupoid_laws φ).2.2.2.1
  inverse_source := (atlasGroupoid_laws φ).2.2.2.2.1
  inverse_target := (atlasGroupoid_laws φ).2.2.2.2.2.1
  associativity := (atlasGroupoid_laws φ).2.2.2.2.2.2.1
  right_identity := (atlasGroupoid_laws φ).2.2.2.2.2.2.2.1
  left_identity := (atlasGroupoid_laws φ).2.2.2.2.2.2.2.2.1
  inverse_comp := (atlasGroupoid_laws φ).2.2.2.2.2.2.2.2.2.1
  comp_inverse := (atlasGroupoid_laws φ).2.2.2.2.2.2.2.2.2.2

/-- The object scheme of `atlasGroupoid φ` is the domain of the atlas. -/
theorem atlasGroupoid_U (φ : ofOver U ⟶ X) [Etale φ] : (atlasGroupoid φ).U = U :=
  rfl

/-- The arrow scheme of `atlasGroupoid φ` is the kernel pair `U ×_X U`. -/
theorem atlasGroupoid_R (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).R = (atlasRelation φ).left :=
  rfl

/-- The source map of `atlasGroupoid φ` is the second kernel-pair projection. -/
theorem atlasGroupoid_s (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).s = (atlasRelation φ).s :=
  rfl

/-- The target map of `atlasGroupoid φ` is the first kernel-pair projection. -/
theorem atlasGroupoid_t (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).t = (atlasRelation φ).t :=
  rfl

/-- The composition map of `atlasGroupoid φ` is the internal composition of the kernel pair. -/
theorem atlasGroupoid_c (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).c = (atlasRelation φ).composition :=
  rfl

/-- The identity-arrow map of `atlasGroupoid φ` is the diagonal lift of the kernel pair. -/
theorem atlasGroupoid_e (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).e =
      (atlasEtale φ).rep.lift' (𝟙 U) (𝟙 U) rfl :=
  rfl

/-- The inverse-arrow map of `atlasGroupoid φ` is the swap lift of the kernel pair. -/
theorem atlasGroupoid_i (φ : ofOver U ⟶ X) [Etale φ] :
    (atlasGroupoid φ).i =
      (atlasEtale φ).rep.lift' ((atlasEtale φ).rep.snd φ) ((atlasEtale φ).rep.fst' φ)
        ((atlasEtale φ).rep.isPullback' φ).w.symm :=
  rfl

/-- The two projections of the represented atlas kernel pair have equal composites with
the atlas morphism. -/
theorem atlasGroupoid_comp_eq (φ : ofOver U ⟶ X) [Etale φ] :
    ofOverMap (atlasGroupoid φ).t ≫ φ = ofOverMap (atlasGroupoid φ).s ≫ φ :=
  sorry

/-- The kernel-pair projections of an étale atlas are étale, they equalize `φ` after
`ofOverMap`, and composition recovers the source and target of composable arrows. -/
theorem atlasGroupoid_spec (φ : ofOver U ⟶ X) [Etale φ] :
    AlgebraicGeometry.Etale (atlasGroupoid φ).t.left ∧
      AlgebraicGeometry.Etale (atlasGroupoid φ).s.left ∧
        ofOverMap (atlasGroupoid φ).t ≫ φ = ofOverMap (atlasGroupoid φ).s ≫ φ ∧
          (atlasGroupoid φ).c ≫ (atlasGroupoid φ).t =
            pullback.fst (atlasGroupoid φ).s (atlasGroupoid φ).t ≫ (atlasGroupoid φ).t ∧
            (atlasGroupoid φ).c ≫ (atlasGroupoid φ).s =
              pullback.snd (atlasGroupoid φ).s (atlasGroupoid φ).t ≫ (atlasGroupoid φ).s :=
  ⟨(etale_projections φ (atlasEtale φ)).1,
    (etale_projections φ (atlasEtale φ)).2, atlasGroupoid_comp_eq φ,
    (atlasGroupoid φ).comp_target, (atlasGroupoid φ).comp_source⟩

end AlgebraicGeometry.AlgebraicSpace
