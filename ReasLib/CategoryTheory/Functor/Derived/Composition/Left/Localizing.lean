/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.Composition.Left
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Localizing
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Left-Derived Composition on a Localizing Generator

This leaf upgrades the componentwise comparison theorem for chosen left-derived models to a
natural isomorphism when one localized source object generates the whole source category. The
isomorphism-locus closure assumptions remain explicit: in applications they are supplied by
exactness and preservation of coproducts.
-/

open CategoryTheory.Limits

universe vA vB vC vDA vDB vE uA uB uC uDA uDB uE

namespace CategoryTheory.Functor.LeftDerived.Composition

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {DA : Type uDA} {DB : Type uDB}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vDA} DA] [Category.{vDB} DB]
  [HasZeroObject DA] [Preadditive DA] [HasShift DA ℤ]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA]
  {F : A ⥤ B} {G : B ⥤ C} {L : A ⥤ DA} {L' : B ⥤ DB}
  {LF : DA ⥤ DB} {LG : DB ⥤ C} {LGF : DA ⥤ C}

namespace Localizing

/-- If one localized source object locally generates the source of the chosen models, the three
counits are invertible at that object, and the comparison isomorphism locus is localizing, then
the comparison between the iterated and direct left-derived models is an isomorphism. -/
@[stacks 0BZ3 "left-derived composition from a localizing generator"]
theorem isIso
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L') (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S] [LGF.IsLeftDerivedFunctor εGF S]
    (X : A)
    (h_generate : (ObjectProperty.singleton (L.obj X)).IsLocalizingGenerator)
    (h_localizing :
      (NatTrans.isomorphismLocus (comparisonOfModels S εF εG εGF)).IsLocalizing)
    [IsIso (εF.app X)] [IsIso (εG.app (F.obj X))] [IsIso (εGF.app X)] :
    IsIso (comparisonOfModels S εF εG εGF) := by
  apply NatTrans.isIso_of_localizingGenerator
    (comparisonOfModels S εF εG εGF) (ObjectProperty.singleton (L.obj X))
      h_generate ?_ h_localizing
  rw [ObjectProperty.singleton_le_iff]
  infer_instance

/-- The localizing-generator criterion is unchanged when the object computing the second model
is presented only up to isomorphism. This is the form used for tensor products, where the value
of the first tensor functor is canonically identified with the underlying bimodule. -/
@[stacks 0BZ3 "left-derived composition with an identified generator image"]
theorem isIso_of_obj_iso
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L') (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S] [LGF.IsLeftDerivedFunctor εGF S]
    (X : A) (Y : B) (e : F.obj X ≅ Y)
    (h_generate : (ObjectProperty.singleton (L.obj X)).IsLocalizingGenerator)
    (h_localizing :
      (NatTrans.isomorphismLocus (comparisonOfModels S εF εG εGF)).IsLocalizing)
    [IsIso (εF.app X)] [IsIso (εG.app Y)] [IsIso (εGF.app X)] :
    IsIso (comparisonOfModels S εF εG εGF) := by
  haveI : IsIso (εG.app (F.obj X)) :=
    (NatTrans.isIso_app_iff_of_iso εG e).2 inferInstance
  exact isIso S εF εG εGF X h_generate h_localizing

/-- If the second underived functor already inverts its localization class, the second counit is
an isomorphism. Hence invertibility of the other two counits on a localizing source generator
upgrades the comparison between the iterated and direct chosen left-derived models to a natural
isomorphism. -/
theorem isIso_of_second_inverts
    (S : MorphismProperty A) (S' : MorphismProperty B)
    (εF : L ⋙ LF ⟶ F ⋙ L') (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S] [L'.IsLocalization S']
    [LG.IsLeftDerivedFunctor εG S'] [LGF.IsLeftDerivedFunctor εGF S]
    (hG : S'.IsInvertedBy G) (X : A)
    (h_generate : (ObjectProperty.singleton (L.obj X)).IsLocalizingGenerator)
    (h_localizing :
      (NatTrans.isomorphismLocus (comparisonOfModels S εF εG εGF)).IsLocalizing)
    [IsIso (εF.app X)] [IsIso (εGF.app X)] :
    IsIso (comparisonOfModels S εF εG εGF) := by
  letI : IsIso εG := Functor.isIso_of_isLeftDerivedFunctor_of_inverts LG εG hG
  exact isIso S εF εG εGF X h_generate h_localizing

section GeneratedImage

variable [HasZeroObject B] [Preadditive B] [HasShift B ℤ]
  [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]

/-- Suppose the image `Y` of a source generator is built from an object `Z` by localizing
operations. If the second counit is invertible at `Z`, its isomorphism locus is localizing, and
the comparison locus is localizing, then the comparison between the iterated and direct chosen
left-derived models is an isomorphism. This separates cellular or semi-free induction from the
particular natural transformation to which it is applied. -/
@[stacks 0BZ5 "left-derived composition from a generated functor image"]
theorem isIso_of_generatedImage
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L') (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S] [LGF.IsLeftDerivedFunctor εGF S]
    (X : A) (Y Z : B) (e : F.obj X ≅ Y)
    (hY : (ObjectProperty.singleton Z).localizingClosure Y)
    (h_second_localizing : (NatTrans.isomorphismLocus εG).IsLocalizing)
    (h_generate : (ObjectProperty.singleton (L.obj X)).IsLocalizingGenerator)
    (h_localizing :
      (NatTrans.isomorphismLocus (comparisonOfModels S εF εG εGF)).IsLocalizing)
    [IsIso (εF.app X)] [IsIso (εG.app Z)] [IsIso (εGF.app X)] :
    IsIso (comparisonOfModels S εF εG εGF) := by
  haveI : IsIso (εG.app Y) :=
    NatTrans.isIso_app_of_mem_localizingClosure εG (ObjectProperty.singleton Z) Y hY
      (by
        rw [ObjectProperty.singleton_le_iff]
        infer_instance)
      h_second_localizing
  exact isIso_of_obj_iso S εF εG εGF X Y e h_generate h_localizing

end GeneratedImage

section GeneratedImages

variable {E : Type uE} [Category.{vE} E]
  [HasZeroObject B] [Preadditive B] [HasShift B ℤ]
  [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [HasZeroObject E] [Preadditive E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  {G₂ : B ⥤ E ⥤ C} {LG₂ : DB ⥤ E ⥤ C} {LGF₂ : DA ⥤ E ⥤ C}

/-- Suppose the image `Y` of the source generator is locally generated by `Z`, while the
second input category is locally generated by `W`. If the two-variable second counit is an
isomorphism at `(Z, W)` and its isomorphism loci are localizing successively in both variables,
then the comparison between the iterated and direct left-derived models is an isomorphism.

This is the symmetric cellular-induction form used for tensor products of two semi-free
bimodules: the free-free comparison is the only componentwise base case. -/
@[stacks 0BZ5 "left-derived composition from two generated inputs"]
theorem isIso_of_generatedImages
    (S : MorphismProperty A)
    (εF : L ⋙ LF ⟶ F ⋙ L') (εG : L' ⋙ LG₂ ⟶ G₂)
    (εGF : L ⋙ LGF₂ ⟶ F ⋙ G₂)
    [L.IsLocalization S] [LGF₂.IsLeftDerivedFunctor εGF S]
    (X : A) (Y Z : B) (W : E) (e : F.obj X ≅ Y)
    (hY : (ObjectProperty.singleton Z).localizingClosure Y)
    (h_second_generator : (ObjectProperty.singleton W).IsLocalizingGenerator)
    (h_second_inner : (NatTrans.isomorphismLocus (εG.app Z)).IsLocalizing)
    (h_second_outer : (NatTrans.isomorphismLocus εG).IsLocalizing)
    (h_generate : (ObjectProperty.singleton (L.obj X)).IsLocalizingGenerator)
    (h_localizing :
      (NatTrans.isomorphismLocus (comparisonOfModels S εF εG εGF)).IsLocalizing)
    [IsIso (εF.app X)] [IsIso ((εG.app Z).app W)] [IsIso (εGF.app X)] :
    IsIso (comparisonOfModels S εF εG εGF) := by
  haveI : IsIso (εG.app Z) :=
    NatTrans.isIso_of_localizingGenerator (εG.app Z) (ObjectProperty.singleton W)
      h_second_generator
      (by
        rw [ObjectProperty.singleton_le_iff]
        infer_instance)
      h_second_inner
  haveI : IsIso (εG.app Y) :=
    NatTrans.isIso_app_of_mem_localizingClosure εG (ObjectProperty.singleton Z) Y hY
      (by
        rw [ObjectProperty.singleton_le_iff]
        infer_instance)
      h_second_outer
  exact isIso_of_obj_iso S εF εG εGF X Y e h_generate h_localizing

end GeneratedImages

end Localizing

end CategoryTheory.Functor.LeftDerived.Composition
