/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.PointwiseValue
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Functoriality
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit.Functoriality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointwise derived adjunctions

@stack 0FND

An adjunction `G ⊣ F` identifies the Hom-sets between a pointwise left-derived value of `G`
and a pointwise right-derived value of `F`.  The construction is independent of triangulated
structure: it only uses the two localization systems, their calculi of fractions, and essential
constancy at the two objects in question.

The forward and inverse functions below are explicit.  They use the selected essentially
constant presentations and the concrete left- and right-fraction quotient models; no
equivalence is selected from an existence theorem.  The inverse laws, denominator formula, and
two-variable naturality are proposition-valued proof obligations.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  {F : D ⥤ D'} {G : D' ⥤ D}

namespace Pointwise

namespace Forward

/-- The forward generator map: a right fraction representing a morphism into the selected
right-derived stage is sent across the underived adjunction and the selected stage map to `K`. -/
noncomputable def stage
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    (V : (MorphismProperty.Over S' ⊤ M)ᵒᵖ) :
    (RightFraction.Localization.homDiagram S' M
      (F.obj hK.stage.left)).obj V →
      (CategoryTheory.Functor.LeftDerived.Value.obj (G ⋙ S.Q) S' M ⟶ S.Q.obj K) :=
  fun φ ↦
    CategoryTheory.Functor.LeftDerived.Value.π (X := M) (G ⋙ S.Q) S' V.unop.hom V.unop.prop ≫
      S.Q.map ((adj.homEquiv V.unop.left
        hK.stage.left).symm φ.down) ≫
      hK.stage.hom

/-- The forward generator maps are compatible with refinement of right fractions. -/
theorem stage_naturality
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    {V W : (MorphismProperty.Over S' ⊤ M)ᵒᵖ} (a : V ⟶ W) :
    Function.comp (stage adj S S' K M W)
        ((RightFraction.Localization.homDiagram S' M
          (F.obj hK.stage.left)).map a) =
      stage adj S S' K M V := sorry

/-- The cocone of forward generator maps on the concrete right-fraction Hom diagram. -/
noncomputable def cocone
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M] :
    (RightFraction.Localization.homDiagram S' M
      (F.obj hK.stage.left)).CoconeTypes where
  pt := CategoryTheory.Functor.LeftDerived.Value.obj (G ⋙ S.Q) S' M ⟶ S.Q.obj K
  ι := stage adj S S' K M
  ι_naturality := stage_naturality adj S S' K M

end Forward

/-- The explicit forward pointwise-derived adjunction map.  It first retracts to the selected
right-derived stage, expands the resulting localized morphism as a right fraction, and maps its
numerator across `adj`. -/
@[stacks 0FND]
noncomputable def forward
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S'.HasRightCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M] :
    ((S'.Q.obj M) ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K) →
      (CategoryTheory.Functor.LeftDerived.Value.obj (G ⋙ S.Q) S' M ⟶ S.Q.obj K) :=
  fun f ↦
    (RightFraction.Localization.homDiagram S' M
      (F.obj hK.stage.left)).descColimitType
        (Forward.cocone adj S S' K M)
        ((RightFraction.Localization.homColimit.typeEquivTo S'.Q S' M
          (F.obj hK.stage.left)).symm
            (f ≫ hK.presentationIso.inv ≫ hK.splitEpi.section_))

namespace Backward

/-- The inverse generator map: a left fraction representing a morphism out of the selected
left-derived stage is sent across the underived adjunction and into the right-derived value. -/
noncomputable def stage
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    (U : MorphismProperty.Under S ⊤ K) :
    (LeftFraction.Localization.homDiagram S
      (G.obj hM.stage.right) K).obj U →
      ((S'.Q.obj M) ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K) :=
  fun ψ ↦
    hM.stage.hom ≫
      S'.Q.map (adj.homEquiv hM.stage.right U.right ψ.down) ≫
      CategoryTheory.Functor.RightDerived.Value.ι (X := K) (F ⋙ S'.Q) S U.hom U.prop

/-- The inverse generator maps are compatible with refinement of left fractions. -/
theorem stage_naturality
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    {U V : MorphismProperty.Under S ⊤ K} (a : U ⟶ V) :
    Function.comp (stage adj S S' K M V)
        ((LeftFraction.Localization.homDiagram S
          (G.obj hM.stage.right) K).map a) =
      stage adj S S' K M U := sorry

/-- The cocone of inverse generator maps on the concrete left-fraction Hom diagram. -/
noncomputable def cocone
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M] :
    (LeftFraction.Localization.homDiagram S
      (G.obj hM.stage.right) K).CoconeTypes where
  pt := (S'.Q.obj M) ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K
  ι := stage adj S S' K M
  ι_naturality := stage_naturality adj S S' K M

end Backward

/-- The explicit inverse pointwise-derived adjunction map.  It retracts to the selected
left-derived stage, expands the resulting localized morphism as a left fraction, and maps its
numerator across `adj`. -/
@[stacks 0FND]
noncomputable def backward
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions]
    [hK : Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [hM : Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M] :
    (CategoryTheory.Functor.LeftDerived.Value.obj (G ⋙ S.Q) S' M ⟶ S.Q.obj K) →
      ((S'.Q.obj M) ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K) :=
  fun f ↦
    (LeftFraction.Localization.homDiagram S
      (G.obj hM.stage.right) K).descColimitType
        (Backward.cocone adj S S' K M)
        ((LeftFraction.Localization.homColimit.typeEquivTo S.Q S
          (G.obj hM.stage.right) K).symm
            (hM.splitMono.retraction ≫ hM.presentationIso.hom ≫ f))

/-- The explicit backward map is a left inverse to the explicit forward map. -/
@[stacks 0FND]
theorem backward_forward
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    (f : (S'.Q.obj M) ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K) :
    backward adj S S' K M (forward adj S S' K M f) = f := sorry

/-- The explicit forward map is a left inverse to the explicit backward map. -/
@[stacks 0FND]
theorem forward_backward
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    (f : CategoryTheory.Functor.LeftDerived.Value.obj (G ⋙ S.Q) S' M ⟶ S.Q.obj K) :
    forward adj S S' K M (backward adj S S' K M f) = f := sorry

/-- Lemma 13.30.1 (Stacks 0FND), in its category-theoretic form: pointwise left and right
derived values of an adjoint pair satisfy the expected Hom-set equivalence.  Triangulated
structure is not needed for this local comparison. -/
@[stacks 0FND]
noncomputable def homEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M] :
    ((S'.Q.obj M) ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K) ≃
      (CategoryTheory.Functor.LeftDerived.Value.obj (G ⋙ S.Q) S' M ⟶ S.Q.obj K) where
  toFun := forward adj S S' K M
  invFun := backward adj S S' K M
  left_inv := backward_forward adj S S' K M
  right_inv := forward_backward adj S S' K M

namespace HomEquiv

/-- A pointwise-derived Hom-equivalence is canonical when it sends every pair of denominator
generators to the morphism obtained from the underived adjunction. -/
@[stacks 0FND]
def IsCanonical
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    (e : ((S'.Q.obj M) ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K) ≃
      (CategoryTheory.Functor.LeftDerived.Value.obj (G ⋙ S.Q) S' M ⟶ S.Q.obj K)) : Prop :=
  ∀ {K' : D} {M' : D'} (m : M ⟶ M') (hm : S' m) (k : K ⟶ K') (hk : S k)
      (φ : M' ⟶ F.obj K'),
    e ((Localization.isoOfHom S'.Q S' m hm).hom ≫ S'.Q.map φ ≫
        CategoryTheory.Functor.RightDerived.Value.ι (F ⋙ S'.Q) S k hk) =
      CategoryTheory.Functor.LeftDerived.Value.π (G ⋙ S.Q) S' (𝟙 M) (S'.id_mem M) ≫
        S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
        (Localization.isoOfHom S.Q S k hk).inv

end HomEquiv

/-- The pointwise-derived Hom-equivalence satisfies the canonical denominator formula. -/
@[stacks 0FND]
theorem HomEquiv.isCanonical
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M] :
    HomEquiv.IsCanonical adj S S' K M (homEquiv adj S S' K M) := sorry

/-- Computation of the pointwise-derived Hom-equivalence on two denominator generators. -/
@[stacks 0FND]
theorem HomEquiv.spec
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    {K' : D} {M' : D'} (m : M ⟶ M') (hm : S' m) (k : K ⟶ K') (hk : S k)
    (φ : M' ⟶ F.obj K') :
    homEquiv adj S S' K M
        ((Localization.isoOfHom S'.Q S' m hm).hom ≫ S'.Q.map φ ≫
          CategoryTheory.Functor.RightDerived.Value.ι (F ⋙ S'.Q) S k hk) =
      CategoryTheory.Functor.LeftDerived.Value.π (G ⋙ S.Q) S' (𝟙 M) (S'.id_mem M) ≫
        S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
        (Localization.isoOfHom S.Q S k hk).inv := sorry

/-- Naturality of the pointwise-derived Hom-equivalence in the left-derived variable. -/
@[stacks 0FND]
theorem HomEquiv.naturality_left
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    {K : D} {M₁ M₂ : D'}
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M₁]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M₂]
    (m : M₁ ⟶ M₂) (f : S'.Q.obj M₂ ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K) :
    homEquiv adj S S' K M₁ (S'.Q.map m ≫ f) =
      CategoryTheory.Functor.LeftDerived.Value.map (G ⋙ S.Q) S' m ≫
        homEquiv adj S S' K M₂ f := sorry

/-- Naturality of the pointwise-derived Hom-equivalence in the right-derived variable. -/
@[stacks 0FND]
theorem HomEquiv.naturality_right
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    {K₁ K₂ : D} {M : D'}
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K₁]
    [Functor.RightDerived.DefinedAt (F ⋙ S'.Q) S K₂]
    [Functor.LeftDerived.DefinedAt (G ⋙ S.Q) S' M]
    (k : K₁ ⟶ K₂) (f : S'.Q.obj M ⟶ CategoryTheory.Functor.RightDerived.Value.obj (F ⋙ S'.Q) S K₁) :
    homEquiv adj S S' K₂ M
        (f ≫ CategoryTheory.Functor.RightDerived.Value.map (F ⋙ S'.Q) S k) =
      homEquiv adj S S' K₁ M f ≫ S.Q.map k := sorry

end Pointwise

end CategoryTheory.Adjunction
