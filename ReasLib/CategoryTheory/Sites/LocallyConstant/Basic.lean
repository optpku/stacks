/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Locally constant sheaves on a site

This leaf owns the site-theoretic notion of a locally constant sheaf, its
explicit constant-model interface, and the comparison between a constant sheaf
and its restriction to a slice site.
-/

@[expose] public section

universe u v w w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

section LocallyConstant

variable {D : Type w} [Category.{w'} D]
variable [HasWeakSheafify J D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]

/-- A sheaf is locally constant with models satisfying `P` when every slice site admits a
covering by restrictions isomorphic to constant sheaves whose values satisfy `P`. -/
class IsLocallyConstantWith (P : D → Prop) (F : Sheaf J D) : Prop where
  /-- Every object admits a covering by constant models satisfying `P`. -/
  existsConstantCover (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ∃ E : D, P E ∧
        Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) D).obj E)

/-- A sheaf is locally constant when every slice site admits a covering by restrictions
isomorphic to constant sheaves. -/
abbrev IsLocallyConstant (F : Sheaf J D) : Prop :=
  IsLocallyConstantWith (J := J) (fun _ ↦ True) F

namespace IsLocallyConstant

/-- The constant charts supplied by a locally constant sheaf. -/
theorem existsConstantCover (F : Sheaf J D) [IsLocallyConstant F] (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, IsConstant (J.over (X i).left) (F.over (X i).left) := sorry

end IsLocallyConstant

/-- The singleton family at the identity of `U` covers the terminal object of the slice site
`J.over U`. -/
theorem identity_singleton_coversTop_over (U : C) :
    (J.over U).CoversTop (fun _ : PUnit => Over.mk (𝟙 U)) := sorry

/-- Explicit local constant models imply local constancy. -/
theorem isLocallyConstant_of_explicit_constant_models {F : Sheaf J D}
    (hF : ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, ∃ E : D,
          Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) D).obj E)) :
    IsLocallyConstant F := sorry

/-- Local constancy with models satisfying an arbitrary predicate implies ordinary local
constancy after forgetting that predicate. -/
theorem isLocallyConstant_of_isLocallyConstantWith
    (P : D → Prop) (F : Sheaf J D) [IsLocallyConstantWith (J := J) P F] :
    IsLocallyConstant F := sorry

/-- Local constancy with models satisfying `P` is invariant under sheaf isomorphism. -/
theorem isLocallyConstantWith_of_iso
    (P : D → Prop) {F G : Sheaf J D} (e : F ≅ G) [IsLocallyConstantWith (J := J) P F] :
    IsLocallyConstantWith (J := J) P G := sorry

/-- The restriction of a global constant sheaf is a local constant model satisfying `P` whenever
its value satisfies `P`. -/
theorem isLocallyConstantWith_of_constant
    {P : D → Prop} {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (E : D) (hE : P E) :
    IsLocallyConstantWith (J := J) P ((constantSheaf J D).obj E) := sorry

/-- The constant presheaf on `Over U` is naturally isomorphic to the pullback of the constant
presheaf on `C`. -/
noncomputable def constantPresheafOverIso (U : C) (E : D) :
    (Functor.const (Over U)ᵒᵖ).obj E ≅
      (Over.forget U).op ⋙ (Functor.const Cᵒᵖ).obj E :=
  Iso.refl _

/-- The whiskered sheafification unit compares the constant presheaf on a slice site with the
restriction of the ambient constant sheaf. -/
noncomputable def constant_presheaf_over_comparison (U : C) (E : D) :
    ((Functor.const (Over U)ᵒᵖ).obj E) ⟶ (((constantSheaf J D).obj E).over U).obj :=
  Functor.whiskerLeft (Over.forget U).op (toSheafify J ((Functor.const Cᵒᵖ).obj E))

/-- The slice constant-presheaf comparison is a local equivalence for concrete coefficients whose
weak equivalences are precisely the locally bijective morphisms. -/
theorem constant_presheaf_over_comparison_is_W
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (U : C) (E : D) :
    (J.over U).W (constant_presheaf_over_comparison (J := J) (D := D) U E) := sorry

/-- Restriction of a constant sheaf to `J.over U` is canonically isomorphic to the constant
sheaf with the same value on that slice site. The construction consumes the named local-equivalence
theorem `constant_presheaf_over_comparison_is_W` instead of rebuilding morphism-specific
injectivity and surjectivity instances. -/
noncomputable def constantSheafOverObjIso
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (U : C) (E : D) :
    ((constantSheaf J D).obj E).over U ≅ (constantSheaf (J.over U) D).obj E := by
  have hW : (J.over U).W (constant_presheaf_over_comparison (J := J) (D := D) U E) :=
    constant_presheaf_over_comparison_is_W (J := J) (D := D) U E
  let e₁ : (constantSheaf (J.over U) D).obj E ≅
      (presheafToSheaf (J.over U) D).obj ((((constantSheaf J D).obj E).over U).obj) := by
    have hIso : IsIso ((presheafToSheaf (J.over U) D).map
        (constant_presheaf_over_comparison (J := J) (D := D) U E)) :=
      ((J.over U).W_iff (A := D)
        (constant_presheaf_over_comparison (J := J) (D := D) U E)).mp hW
    exact @asIso _ _ _ _
      ((presheafToSheaf (J.over U) D).map
        (constant_presheaf_over_comparison (J := J) (D := D) U E)) hIso
  let e₂ : ((constantSheaf J D).obj E).over U ≅
      (presheafToSheaf (J.over U) D).obj ((((constantSheaf J D).obj E).over U).obj) :=
    (fullyFaithfulSheafToPresheaf (J.over U) D).preimageIso
      (isoSheafify (J.over U) (((constantSheaf J D).obj E).over U).property)
  exact e₂ ≪≫ e₁.symm

/-- Restriction of a constant sheaf to a slice site is constant. -/
theorem constant_sheaf_over_isConstant
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (U : C) (E : D) :
    IsConstant (J.over U) (((constantSheaf J D).obj E).over U) := sorry

/-- Ordinary local constancy is invariant under sheaf isomorphism. -/
theorem isLocallyConstant_of_iso
    {F G : Sheaf J D} (e : F ≅ G) [IsLocallyConstant F] :
    IsLocallyConstant G := sorry

/-- A globally constant sheaf is locally constant. -/
theorem isLocallyConstant_of_isConstant
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (F : Sheaf J D) [IsConstant J F] :
    IsLocallyConstant F := sorry

end LocallyConstant

end Sheaf

end CategoryTheory
