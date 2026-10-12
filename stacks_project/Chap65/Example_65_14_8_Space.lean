/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import stacks_project.Chap65.Example_65_14_8_Action
public import stacks_project.Chap65.Lemma_65_14_6_Equivariant

/-!
# The algebraic space 𝔸¹_k / ℤ

This module records the fppf quotient sheaf `X = 𝔸¹_k / ℤ` of the translation action, the
generic-point morphism `γ : Spec(k(x)) ⟶ X`, and the comparison of the self-fibre product of
`γ` with the coproduct `∐_ℤ Spec(k(x))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- The fppf sheaf `X = 𝔸¹_k / ℤ`, obtained by sheafifying the universe-raised quotient
presheaf of `ofAut (action k)`. -/
def sheafOfPoints (k : Type u) [Field k] [CharZero k] :
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)) :=
  (ofAut (action k)).quotientSheaf (Scheme.fppfTopology.over (base k))

/-- `sheafOfPoints k` is the fppf quotient sheaf of the translation pre-relation. -/
theorem sheafOfPoints_eq (k : Type u) [Field k] [CharZero k] :
    sheafOfPoints k =
      (ofAut (action k)).quotientSheaf (Scheme.fppfTopology.over (base k)) := sorry

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶ sheafOfPoints k :=
  (ofAut (action k)).quotientMap (Scheme.fppfTopology.over (base k))

/-- The atlas is the canonical fppf quotient map of `ofAut (action k)`. -/
theorem atlas_eq (k : Type u) [Field k] [CharZero k] :
    atlas k = (ofAut (action k)).quotientMap (Scheme.fppfTopology.over (base k)) := sorry

/-- The diagonal of `X = 𝔸¹_k / ℤ` is representable relative to `uliftYoneda`. -/
theorem representableDiagonal_sheafOfPoints (k : Type u) [Field k] [CharZero k] :
    uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := sorry

/-- The atlas `U ⟶ X` is representable and étale relative to `uliftYoneda`. -/
theorem atlas_etale (k : Type u) [Field k] [CharZero k] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom := sorry

/-- The atlas `U ⟶ X` is étale-locally surjective. -/
theorem atlas_locallySurjective (k : Type u) [Field k] [CharZero k] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom := sorry

/-- The residue field `k(x)` of the generic point of `𝔸¹_k`. -/
abbrev genericResidueField (k : Type u) [Field k] [CharZero k] : Type u :=
  ResidueField ((cover k).left.presheaf.stalk (genericPoint (cover k).left))

/-- `genericResidueField k` is the residue field of the stalk at the generic point. -/
theorem genericResidueField_eq (k : Type u) [Field k] [CharZero k] :
    genericResidueField k =
      ResidueField ((cover k).left.presheaf.stalk (genericPoint (cover k).left)) :=
  sorry

/-- The residue field of the generic point of `𝔸¹_k` is a field. -/
instance instField_genericResidueField (k : Type u) [Field k] [CharZero k] :
    Field (genericResidueField k) := inferInstance

/-- The structure morphism `Spec(k(x)) ⟶ Spec k` of the generic point. -/
def genericStructure (k : Type u) [Field k] [CharZero k] :
    Spec (CommRingCat.of (genericResidueField k)) ⟶ base k :=
  (cover k).left.fromSpecResidueField (genericPoint (cover k).left) ≫ (cover k).hom

/-- `genericStructure k` is the composite of `fromSpecResidueField` with the structure
morphism of the affine line. -/
theorem genericStructure_eq (k : Type u) [Field k] [CharZero k] :
    genericStructure k =
      (cover k).left.fromSpecResidueField (genericPoint (cover k).left) ≫ (cover k).hom :=
  sorry

/-- The `k`-algebra structure on `k(x)` induced by the structure morphism of `Spec(k(x))`. -/
instance instAlgebra_genericResidueField (k : Type u) [Field k] [CharZero k] :
    Algebra k (genericResidueField k) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (genericStructure k).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (genericResidueField k))).hom).hom.toAlgebra

/-- `Spec(k(x))` as a scheme over `Spec k`. -/
abbrev genericOver (k : Type u) [Field k] [CharZero k] : Over (base k) :=
  specOver (genericStructure k)

/-- `genericOver k` is `specOver` of the generic-point structure morphism. -/
theorem genericOver_eq (k : Type u) [Field k] [CharZero k] :
    genericOver k = specOver (genericStructure k) := sorry

/-- The triangle identity for the generic-point morphism into the affine line. -/
theorem genericToCover_w (k : Type u) [Field k] [CharZero k] :
    (cover k).left.fromSpecResidueField (genericPoint (cover k).left) ≫ (cover k).hom =
      (genericOver k).hom := sorry

/-- The closed generic-point morphism `Spec(k(x)) ⟶ 𝔸¹_k` over `Spec k`. -/
def genericToCover (k : Type u) [Field k] [CharZero k] : genericOver k ⟶ cover k :=
  Over.homMk ((cover k).left.fromSpecResidueField (genericPoint (cover k).left))
    (genericToCover_w k)

/-- The underlying scheme morphism of `genericToCover` is `fromSpecResidueField` at the
generic point. -/
theorem genericToCover_left (k : Type u) [Field k] [CharZero k] :
    (genericToCover k).left =
      (cover k).left.fromSpecResidueField (genericPoint (cover k).left) := sorry

/-- The morphism `γ : Spec(k(x)) ⟶ X` of the generic point of the affine line into the
quotient. -/
def genericHom (k : Type u) [Field k] [CharZero k] :
    specToQuotientHom (action k) (genericStructure k) :=
  (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericToCover k) ≫ atlas k

/-- `genericHom k` is the composite of the represented generic-point map with the atlas. -/
theorem genericHom_eq (k : Type u) [Field k] [CharZero k] :
    genericHom k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericToCover k) ≫
        atlas k := sorry

/-- The generic-point morphism to `U` lifts `γ` along the atlas `U ⟶ X`. -/
theorem isQuotientLift_genericToCover (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericToCover k) ≫ atlas k =
      genericHom k := sorry

/-- `γ` does not factor through any monomorphism `Spec(L) ⟶ X` from the spectrum of a field. -/
theorem not_exists_mono_factor (k : Type u) [Field k] [CharZero k] :
    ¬ ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
        (ι : specToQuotientHom (action k) (FieldExtension.specMap k L))
        (hι : CategoryTheory.Mono ι)
        (φ : genericOver k ⟶ specOver (FieldExtension.specMap k L)),
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map φ ≫ ι = genericHom k :=
  sorry

/-- Any factorization of `γ` through a monomorphism `Spec(L) ⟶ X` has `k(x) = L`. -/
theorem isIso_of_mono_factor (k : Type u) [Field k] [CharZero k]
    {L : Type u} [Field L] [Algebra k L]
    (ι : specToQuotientHom (action k) (FieldExtension.specMap k L))
    (φ : genericOver k ⟶ specOver (FieldExtension.specMap k L))
    (hι : CategoryTheory.Mono ι)
    (hφ :
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map φ ≫ ι = genericHom k) :
    IsIso φ.left := sorry

/-- The morphism `γ` is not a monomorphism of fppf sheaves. -/
theorem not_mono_genericHom (k : Type u) [Field k] [CharZero k] :
    ¬ CategoryTheory.Mono (genericHom k) := sorry

/-- Finite subgroups of the acting copy of `ℤ` are trivial. -/
theorem finite_subgroup_eq_bot (H : Subgroup group) [Finite H] : H = ⊥ := sorry

/-- The coproduct `∐_ℤ Spec(k(x))`, i.e. the scheme `Spec(k(x)) × ℤ`. -/
def genericCoproduct (k : Type u) [Field k] [CharZero k] : Over (base k) :=
  ∐ fun _ : group ↦ genericOver k

/-- `genericCoproduct k` is the coproduct of copies of `Spec(k(x))` indexed by `ℤ`. -/
theorem genericCoproduct_eq (k : Type u) [Field k] [CharZero k] :
    genericCoproduct k = ∐ fun _ : group ↦ genericOver k := sorry

/-- The inclusion of the `g`-summand of `Spec(k(x)) × ℤ`. -/
def genericCoproductι (k : Type u) [Field k] [CharZero k] (g : group) :
    genericOver k ⟶ genericCoproduct k :=
  Sigma.ι (fun _ : group ↦ genericOver k) g

/-- `genericCoproductι k g` is the coproduct inclusion of the `g`-summand. -/
theorem genericCoproductι_eq (k : Type u) [Field k] [CharZero k] (g : group) :
    genericCoproductι k g = Sigma.ι (fun _ : group ↦ genericOver k) g := sorry

/-- The triangle identity for the automorphism of `Spec(k(x))` induced by translation. -/
theorem genericAut_w (k : Type u) [Field k] [CharZero k] (g : group) :
    Spec.map (genericResidueAut k g) ≫ (genericOver k).hom = (genericOver k).hom := sorry

/-- The automorphism of `Spec(k(x))` over `Spec k` induced by translation by `g`. -/
def genericAut (k : Type u) [Field k] [CharZero k] (g : group) :
    genericOver k ⟶ genericOver k :=
  Over.homMk (Spec.map (genericResidueAut k g)) (genericAut_w k g)

/-- The underlying scheme morphism of `genericAut k g` is `Spec.map` of the residue-field
automorphism. -/
theorem genericAut_left (k : Type u) [Field k] [CharZero k] (g : group) :
    (genericAut k g).left = Spec.map (genericResidueAut k g) := sorry

/-- The first projection of the coproduct cone, sending the `g`-summand by translation by `g`. -/
def genericCoproductFst (k : Type u) [Field k] [CharZero k] :
    genericCoproduct k ⟶ genericOver k :=
  Sigma.desc fun g : group ↦ genericAut k g

/-- `genericCoproductFst` is the coproduct fold of the translation automorphisms. -/
theorem genericCoproductFst_eq (k : Type u) [Field k] [CharZero k] :
    genericCoproductFst k = Sigma.desc fun g : group ↦ genericAut k g := sorry

/-- The second projection of the coproduct cone, sending every summand by the identity. -/
def genericCoproductSnd (k : Type u) [Field k] [CharZero k] :
    genericCoproduct k ⟶ genericOver k :=
  Sigma.desc fun _ : group ↦ 𝟙 (genericOver k)

/-- `genericCoproductSnd` is the coproduct fold of identities. -/
theorem genericCoproductSnd_eq (k : Type u) [Field k] [CharZero k] :
    genericCoproductSnd k = Sigma.desc fun _ : group ↦ 𝟙 (genericOver k) := sorry

/-- The two folds of `Spec(k(x)) × ℤ` become equal after composing with `γ`. -/
theorem genericCoproduct_equalizes (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductFst k) ≫
        genericHom k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductSnd k) ≫
        genericHom k := sorry

/-- Translation by `g` on `Spec(k(x))` does not change the composite with `γ`. -/
theorem genericAut_comp_genericHom (k : Type u) [Field k] [CharZero k] (g : group) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericAut k g) ≫ genericHom k =
      genericHom k := sorry

/-- The component map of the coproduct cone into the self-fibre product of `γ`. -/
def genericPullbackComponent (k : Type u) [Field k] [CharZero k] (g : group) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (genericOver k) ⟶
      pullback (genericHom k) (genericHom k) :=
  pullback.lift
    ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericAut k g))
    ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (𝟙 (genericOver k)))
    (genericAut_comp_genericHom k g)

/-- `genericPullbackComponent k g` is the pullback lift of `(genericAut g, id)`. -/
theorem genericPullbackComponent_eq (k : Type u) [Field k] [CharZero k] (g : group) :
    genericPullbackComponent k g =
      pullback.lift
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericAut k g))
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (𝟙 (genericOver k)))
        (genericAut_comp_genericHom k g) := sorry

/-- The comparison `Spec(k(x)) × ℤ ⟶ Spec(k(x)) ×_X Spec(k(x))` sending the `g`-summand
by the pair `(g·η, η)`. -/
def genericPullbackIso_inv (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (genericCoproduct k) ⟶
      pullback (genericHom k) (genericHom k) :=
  pullback.lift
    ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductFst k))
    ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductSnd k))
    (genericCoproduct_equalizes k)

/-- `genericPullbackIso_inv` is the pullback lift of the two coproduct folds. -/
theorem genericPullbackIso_inv_eq (k : Type u) [Field k] [CharZero k] :
    genericPullbackIso_inv k =
      pullback.lift
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductFst k))
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductSnd k))
        (genericCoproduct_equalizes k) := sorry

/-- The first projection of `genericPullbackIso_inv` is represented by `genericCoproductFst`. -/
theorem genericPullbackIso_inv_fst (k : Type u) [Field k] [CharZero k] :
    genericPullbackIso_inv k ≫ pullback.fst (genericHom k) (genericHom k) =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductFst k) :=
  sorry

/-- The second projection of `genericPullbackIso_inv` is represented by `genericCoproductSnd`. -/
theorem genericPullbackIso_inv_snd (k : Type u) [Field k] [CharZero k] :
    genericPullbackIso_inv k ≫ pullback.snd (genericHom k) (genericHom k) =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (genericCoproductSnd k) :=
  sorry

/-- The comparison `Spec(k(x)) × ℤ ⟶ Spec(k(x)) ×_X Spec(k(x))` is an isomorphism of
fppf sheaves. -/
instance instIsIso_genericPullbackIso_inv (k : Type u) [Field k] [CharZero k] :
    IsIso (genericPullbackIso_inv k) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
