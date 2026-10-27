/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A monomorphism of finite étale covers is a monomorphism of schemes. -/
theorem mono_left {X : Scheme.{u}} {Y Z : FiniteEtale X}
    (i : Y ⟶ Z) [Mono i] : Mono i.left := by
  letI : MorphismProperty.HasOfPostcompProperty
      finiteEtaleMorphism finiteEtaleMorphism :=
    { of_postcomp := by
        intro Y Z W f g hg hfg
        letI : IsFinite g := hg.1
        letI : IsFinite (f ≫ g) := hfg.1
        exact ⟨IsFinite.of_comp f g,
          MorphismProperty.of_postcomp (W := @Etale) f g hg.2 hfg.2⟩ }
  haveI : Mono ((MorphismProperty.Over.forget finiteEtaleMorphism ⊤ X).map i) :=
    Functor.map_mono _ i
  exact CategoryTheory.Over.mono_left_of_mono
    ((MorphismProperty.Over.forget finiteEtaleMorphism ⊤ X).map i)

/-- A monomorphism of finite étale covers identifies an open subscheme.
The section inverses come from the native flat-monomorphism construction. -/
instance mono_isOpenImmersion {X : Scheme.{u}} {Y Z : FiniteEtale X}
    (i : Y ⟶ Z) [Mono i] : IsOpenImmersion i.left := by
  letI : Mono i.left := mono_left i
  letI : Etale i.left :=
    MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
      i.left Z.hom Z.prop.2 (by rw [MorphismProperty.Over.w i]; exact Y.prop.2)
  exact IsOpenImmersion.of_flat_of_mono i.left

variable {X : Scheme.{u}} {Y Z : FiniteEtale X} (i : Y ⟶ Z) [mono : Mono i]

include mono

/-- The image of a monomorphism of finite étale covers is closed as well as open. -/
theorem mono_isClosed_range : IsClosed (Set.range i.left) := by
  letI : IsFinite Z.hom := Z.prop.1
  letI hsep : IsSeparated Z.hom := IsSeparated.of_isAffineHom Z.hom
  letI hfinite : IsFinite (i.left ≫ Z.hom) := by
    rw [MorphismProperty.Over.w i]
    exact Y.prop.1
  letI : IsFinite i.left := @IsFinite.of_comp Y.left Z.left X i.left Z.hom hfinite hsep
  exact i.left.isClosedMap.isClosed_range

/-- The open complement of the image of a finite étale monomorphism. -/
def monoComplementOpen : Z.left.Opens :=
  ⟨(Set.range i.left)ᶜ, (mono_isClosed_range i).isOpen_compl⟩

/-- The structural morphism of the complementary open subscheme is finite étale. -/
theorem monoComplementOpen_finiteEtale :
    finiteEtaleMorphism ((monoComplementOpen i).ι ≫ Z.hom) := by
  letI : IsClosedImmersion (monoComplementOpen i).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact i.left.isOpenEmbedding.isOpen_range.isClosed_compl
  exact finiteEtaleMorphism.comp_mem _ _ ⟨inferInstance, inferInstance⟩ Z.prop

/-- The actual complementary finite étale cover. -/
def monoComplement : FiniteEtale X where
  toComma := Over.mk ((monoComplementOpen i).ι ≫ Z.hom)
  prop := monoComplementOpen_finiteEtale i

/-- The inclusion of the complementary cover. -/
def monoComplementInclusion : monoComplement i ⟶ Z :=
  MorphismProperty.Over.homMk (monoComplementOpen i).ι (by rfl)

/-- The original cover and its complement form the two pieces of an open cover. -/
def monoComplementCover : Z.left.OpenCover where
  I₀ := Bool
  X b := if b then Y.left else (monoComplementOpen i).toScheme
  f b := by
    cases b
    · exact (monoComplementOpen i).ι
    · exact i.left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    constructor
    · intro z
      by_cases hz : z ∈ Set.range i.left
      · exact ⟨true, hz⟩
      · exact ⟨false, ⟨⟨z, hz⟩, rfl⟩⟩
    · intro b
      cases b <;> dsimp <;> infer_instance

/-- The morphism on each of the two pieces of the complementary open cover. -/
def monoComplementCoverMap {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) (b : Bool) :
    (monoComplementCover i).X b ⟶ T.left := by
  cases b
  · exact g.left
  · exact f.left

/-- Maps on the two disjoint pieces agree on their overlaps. -/
theorem monoComplementCover_compatible {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) :
    ∀ a b,
      pullback.fst ((monoComplementCover i).f a) ((monoComplementCover i).f b) ≫
          monoComplementCoverMap i f g a =
        pullback.snd ((monoComplementCover i).f a) ((monoComplementCover i).f b) ≫
          monoComplementCoverMap i f g b := by
  have empty_overlap (W : Scheme.{u}) (a : W ⟶ Y.left)
      (b : W ⟶ (monoComplementOpen i).toScheme)
      (h : a ≫ i.left = b ≫ (monoComplementOpen i).ι) : IsEmpty W := by
    refine ⟨fun x ↦ ?_⟩
    have hx : i.left (a x) = (b x).val :=
      congrArg (fun k : W ⟶ Z.left ↦ k x) h
    exact (b x).property ⟨a x, hx⟩
  intro a b
  cases a <;> cases b
  · change pullback.fst (monoComplementOpen i).ι (monoComplementOpen i).ι ≫ g.left =
      pullback.snd (monoComplementOpen i).ι (monoComplementOpen i).ι ≫ g.left
    rw [fst_eq_snd_of_mono_eq]
  · change pullback.fst (monoComplementOpen i).ι i.left ≫ g.left =
      pullback.snd (monoComplementOpen i).ι i.left ≫ f.left
    letI : IsEmpty (pullback (C := Scheme) (monoComplementOpen i).ι i.left) :=
      empty_overlap _ (pullback.snd _ _) (pullback.fst _ _) pullback.condition.symm
    exact isInitialOfIsEmpty.hom_ext _ _
  · change pullback.fst i.left (monoComplementOpen i).ι ≫ f.left =
      pullback.snd i.left (monoComplementOpen i).ι ≫ g.left
    letI : IsEmpty (pullback (C := Scheme) i.left (monoComplementOpen i).ι) :=
      empty_overlap _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    exact isInitialOfIsEmpty.hom_ext _ _
  · change pullback.fst i.left i.left ≫ f.left = pullback.snd i.left i.left ≫ f.left
    letI : Mono i.left := mono_left i
    rw [fst_eq_snd_of_mono_eq]

/-- Glue two maps out of the clopen summands using the native scheme open-cover descent. -/
noncomputable def monoComplementDescLeft {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) : Z.left ⟶ T.left :=
  (monoComplementCover i).glueMorphisms
    (monoComplementCoverMap i f g)
    (monoComplementCover_compatible i f g)

/-- The glued morphism lies over the base. -/
theorem monoComplementDescLeft_over {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) :
    monoComplementDescLeft i f g ≫ T.hom = Z.hom := by
  apply (monoComplementCover i).hom_ext
  intro b
  dsimp only [monoComplementDescLeft]
  rw [← Category.assoc, Cover.ι_glueMorphisms]
  cases b
  · exact MorphismProperty.Over.w g
  · exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w i).symm

/-- The coproduct descent morphism has the actual scheme-gluing map as its underlying map. -/
noncomputable def monoComplementDesc {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) : Z ⟶ T :=
  MorphismProperty.Over.homMk (monoComplementDescLeft i f g)
    (monoComplementDescLeft_over i f g)

/-- A finite étale monomorphism and its concrete clopen complement exhibit a binary coproduct. -/
noncomputable def monoComplementIsColimit :
    IsColimit (BinaryCofan.mk i (monoComplementInclusion i)) :=
  BinaryCofan.IsColimit.mk _ (monoComplementDesc i)
    (by
      intro T f g
      apply MorphismProperty.Over.Hom.ext
      change i.left ≫ monoComplementDescLeft i f g = f.left
      exact (monoComplementCover i).ι_glueMorphisms (monoComplementCoverMap i f g)
        (monoComplementCover_compatible i f g) true)
    (by
      intro T f g
      apply MorphismProperty.Over.Hom.ext
      change (monoComplementOpen i).ι ≫ monoComplementDescLeft i f g = g.left
      exact (monoComplementCover i).ι_glueMorphisms (monoComplementCoverMap i f g)
        (monoComplementCover_compatible i f g) false)
    (by
      intro T f g m hf hg
      apply MorphismProperty.Over.Hom.ext
      apply (monoComplementCover i).hom_ext
      intro b
      cases b
      · change (monoComplementOpen i).ι ≫ m.left =
          (monoComplementOpen i).ι ≫ monoComplementDescLeft i f g
        rw [show (monoComplementOpen i).ι ≫ m.left = g.left from
          congrArg (fun k ↦ k.left) hg]
        exact ((monoComplementCover i).ι_glueMorphisms (monoComplementCoverMap i f g)
          (monoComplementCover_compatible i f g) false).symm
      · change i.left ≫ m.left = i.left ≫ monoComplementDescLeft i f g
        rw [show i.left ≫ m.left = f.left from congrArg (fun k ↦ k.left) hf]
        exact ((monoComplementCover i).ι_glueMorphisms (monoComplementCoverMap i f g)
          (monoComplementCover_compatible i f g) true).symm)

/-- Every finite étale monomorphism is the inclusion of a direct summand. -/
theorem monoInducesIsoOnDirectSummand :
    ∃ (W : FiniteEtale X) (j : W ⟶ Z), Nonempty (IsColimit (BinaryCofan.mk i j)) :=
  ⟨monoComplement i, monoComplementInclusion i, ⟨monoComplementIsColimit i⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale
