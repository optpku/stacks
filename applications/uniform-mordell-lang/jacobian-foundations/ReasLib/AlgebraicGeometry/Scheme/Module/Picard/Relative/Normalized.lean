/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Section-normalization design compared with TauCetiProject/TauCeti,
commit 76eb167bacad4b75ea1cb657b4db1d7efb788022,
AlgebraicGeometry/PicardFunctor/Relative.lean (Apache-2.0).
-/
module

public import ReasLib.GroupTheory.QuotientGroup.Splitting
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Quotient

/-!
# Section-normalized relative Picard classes

For a section `P` of `X → S`, relative classes have a unique representative in
the kernel of pullback along `P_T : T → T ×ₛ X`: normalize `L` to
`L - p* P_T* L`. The resulting comparison is natural in every test scheme.
Only a section is needed; no field, curve, properness, structure-sheaf
pushforward condition, or representing scheme occurs here.

The kernel is a derived view of `Scheme.PicardGroup`, not a second owner of
line bundles with a chosen rigidification. Comparing with actual rigidified
objects, and proving their effective descent, are separate tasks.

References: Bosch--Lütkebohmert--Raynaud, Néron Models, §8.1;
Kleiman, The Picard Scheme, §9.2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

/-- Compatibility name for the additive-group construction owned by
`QuotientAddGroup.quotientRangeEquivKer`. -/
abbrev quotientRangeEquivKer {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (i : A →+ B) (r : B →+ A) (h : ∀ a, r (i a) = a) :
    B ⧸ i.range ≃+ r.ker :=
  QuotientAddGroup.quotientRangeEquivKer i r h

variable {S : Scheme.{u}} (X : Over S) (P : 𝟙_ (Over S) ⟶ X)

/-- The base-changed section `P_T : T → T ×ₛ X`. -/
noncomputable def baseChangeSection (T : Over S) : T.left ⟶ (T ⊗ X).left :=
  pullback.lift (𝟙 T.left) (T.hom ≫ P.left) (by simp [Category.assoc, P.w])

/-- The base-changed section splits the projection to the test scheme. -/
@[simp]
theorem baseChangeSection_fst (T : Over S) :
    baseChangeSection X P T ≫ (CartesianMonoidalCategory.fst T X).left = 𝟙 T.left :=
  pullback.lift_fst _ _ _

/-- Section pullback splits pullback of base classes. -/
@[simp]
theorem baseChangeSection_picardPullback (T : Over S) (a : T.left.PicardGroup) :
    Scheme.Hom.picardPullback (baseChangeSection X P T)
      (Scheme.Hom.picardPullback ((CartesianMonoidalCategory.fst T X).left) a) = a := by
  calc
    _ = Scheme.Hom.picardPullback
        (baseChangeSection X P T ≫ (CartesianMonoidalCategory.fst T X).left) a :=
      (Scheme.Hom.picardPullback_comp_apply _ _ a).symm
    _ = a := by
      rw [baseChangeSection_fst]
      exact Scheme.Hom.picardPullback_id_apply a

/-- Classes whose restriction to the chosen section is trivial. -/
noncomputable def normalizedClasses (T : (Over S)ᵒᵖ) :
    AddSubgroup ((groupPresheaf X).obj T) :=
  (Scheme.Hom.picardPullback (baseChangeSection X P T.unop)).ker

/-- Pullback of a normalized class is normalized along the base-changed section. -/
theorem map_mem_normalizedClasses {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    {a : (groupPresheaf X).obj T} (ha : a ∈ normalizedClasses X P T) :
    (groupPresheaf X).map f a ∈ normalizedClasses X P T' := by
  change Scheme.Hom.picardPullback (baseChangeSection X P T'.unop)
      (Scheme.Hom.picardPullback ((f.unop ▷ X).left) a) = 0
  have hs : baseChangeSection X P T'.unop ≫ (f.unop ▷ X).left =
      f.unop.left ≫ baseChangeSection X P T.unop := by
    apply pullback.hom_ext
    · simp [baseChangeSection, Category.assoc]
    · simp [baseChangeSection, Category.assoc]
  rw [← Scheme.Hom.picardPullback_comp_apply, hs,
    Scheme.Hom.picardPullback_comp_apply]
  change Scheme.Hom.picardPullback f.unop.left
    (Scheme.Hom.picardPullback (baseChangeSection X P T.unop) a) = 0
  rw [show Scheme.Hom.picardPullback (baseChangeSection X P T.unop) a = 0 from ha,
    map_zero]

/-- The section-normalized presheaf, retaining addition by tensor product. -/
noncomputable def normalizedPresheaf : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of (normalizedClasses X P T)
  map f := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ⟨(groupPresheaf X).map f a.1, map_mem_normalizedClasses X P f a.2⟩
      map_zero' := by ext; exact map_zero _
      map_add' := by intros; ext; exact map_add _ _ _ }
  map_id T := by ext; simp
  map_comp f g := by ext; simp

/-- Every relative class has a unique section-normalized class. -/
noncomputable def quotientNormalizedEquiv (T : (Over S)ᵒᵖ) :
    (quotientPresheaf X).obj T ≃+ (normalizedPresheaf X P).obj T :=
  QuotientAddGroup.quotientRangeEquivKer
    (Scheme.Hom.picardPullback ((CartesianMonoidalCategory.fst T.unop X).left))
    (Scheme.Hom.picardPullback (baseChangeSection X P T.unop))
    (baseChangeSection_picardPullback X P T.unop)

/-- Normalization subtracts the class pulled back from the restriction to the section. -/
@[simp]
theorem quotientNormalizedEquiv_mk (T : (Over S)ᵒᵖ) (a : (groupPresheaf X).obj T) :
    (quotientNormalizedEquiv X P T (QuotientAddGroup.mk a)).1 =
      a - (show (groupPresheaf X).obj T from
        Scheme.Hom.picardPullback (CartesianMonoidalCategory.fst T.unop X).left
          (Scheme.Hom.picardPullback (baseChangeSection X P T.unop) a)) :=
  QuotientAddGroup.quotientRangeEquivKer_mk _ _ _ a

/-- Forgetting normalization recovers the same relative class. -/
@[simp]
theorem quotientNormalizedEquiv_symm_apply (T : (Over S)ᵒᵖ)
    (a : (normalizedPresheaf X P).obj T) :
    (quotientNormalizedEquiv X P T).symm a = QuotientAddGroup.mk a.1 :=
  QuotientAddGroup.quotientRangeEquivKer_symm_apply _ _ _ a

/-- The quotient and section-normalized presentations agree naturally on all test schemes. -/
noncomputable def quotientNormalizedIso : quotientPresheaf X ≅ normalizedPresheaf X P :=
  (NatIso.ofComponents
    (fun T ↦ (quotientNormalizedEquiv X P T).symm.toAddCommGrpIso)
    (by
      intro T T' f
      ext a
      rfl)).symm

end AlgebraicGeometry.RelativePicard
