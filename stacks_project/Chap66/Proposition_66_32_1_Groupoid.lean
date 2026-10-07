module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Composition
public import stacks_project.Chap65.Lemma_65_9_1
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_18_3_Etale

/-!
# Étale atlas groupoid of an algebraic space

A morphism `φ : U ⟶ X` from a scheme to an algebraic space that is étale as a morphism of
algebraic spaces has kernel pair `R = U ×_X U`. The resulting groupoid scheme
`(U, R, s, t, c)` is the étale groupoid of the atlas `φ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- The representable étale presheaf property of an étale morphism from a scheme to an
algebraic space. -/
theorem atlasEtale (φ : ofOver U ⟶ X) [Etale φ] :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ :=
  (isEtale_iff_isEtaleFromScheme φ).mp inferInstance

/-- `atlasEtale φ` is the étale presheaf property of `φ`. -/
theorem atlasEtale_eq (φ : ofOver U ⟶ X) [Etale φ] :
    atlasEtale φ = (isEtale_iff_isEtaleFromScheme φ).mp inferInstance :=
  rfl

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
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

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
  sorry

/-- The first kernel-pair projection of an étale atlas is étale as a morphism of schemes. -/
instance etale_atlasGroupoid_t {φ : ofOver U ⟶ X} [Etale φ] :
    AlgebraicGeometry.Etale (atlasGroupoid φ).t.left :=
  instEtale_kernelPair_t φ (atlasEtale φ)

/-- The second kernel-pair projection of an étale atlas is étale as a morphism of schemes. -/
instance etale_atlasGroupoid_s {φ : ofOver U ⟶ X} [Etale φ] :
    AlgebraicGeometry.Etale (atlasGroupoid φ).s.left :=
  instEtale_kernelPair_s φ (atlasEtale φ)

end AlgebraicGeometry.AlgebraicSpace
