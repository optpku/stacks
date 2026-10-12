/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap65.Lemma_65_9_1
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap74.Definition_74_22_3_DescentData
public import stacks_project.Chap74.Definition_74_22_11_Effectivity
public import stacks_project.Chap67.Lemma_67_49_5_Normalization

/-!
# Descent data as sheaves over an algebraic space

An fppf covering `{Xᵢ → X}` of algebraic spaces identifies descent data with sheaves
`F` on `(Sch/S)_fppf` over `X` whose pullbacks `Xᵢ ×_X F` are algebraic spaces. The
glued sheaf is the Type `u` sheafification of the coequalizer of the coproduct pair
`∐_{i,j} toSheaf(Vᵢ ×_X Xⱼ) ⇉ ∐ᵢ toSheaf Vᵢ`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of fppf sheaves on `(Sch/S)_fppf` induced by a morphism of algebraic
spaces over `S`. -/
def toSheafMap {S : Scheme.{u}} {F G : AlgebraicSpace S} (φ : F ⟶ G) :
    toSheaf F ⟶ toSheaf G :=
  ObjectProperty.homMk φ

/-- The underlying presheaf morphism of `toSheafMap φ` is `φ`. -/
theorem toSheafMap_hom {S : Scheme.{u}} {F G : AlgebraicSpace S} (φ : F ⟶ G) :
    (toSheafMap φ).hom = φ :=
  rfl

namespace DescentData

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/-- A sheaf `F` over `toSheaf X` is locally an algebraic space along `{Xᵢ → X}` when
each fibre product `Xᵢ ×_X F` is an algebraic space. -/
def locallyAlgebraicSpaceAlong : ObjectProperty (Over (toSheaf X)) :=
  fun F ↦ ∀ i, IsAlgebraicSpace (pullback (toSheafMap (f i)) F.hom).obj

/-- Membership in `locallyAlgebraicSpaceAlong` is componentwise algebraicity of the
fibre products `Xᵢ ×_X F`. -/
theorem mem_locallyAlgebraicSpaceAlong_iff (F : Over (toSheaf X)) :
    locallyAlgebraicSpaceAlong Xᵢ f F ↔
      ∀ i, IsAlgebraicSpace (pullback (toSheafMap (f i)) F.hom).obj :=
  Iff.rfl

/-- The category of sheaves on `(Sch/S)_fppf` over `X` whose pullbacks along the family
`{Xᵢ → X}` are algebraic spaces. -/
abbrev LocallyAlgebraicSpaceAlong :=
  (locallyAlgebraicSpaceAlong Xᵢ f).FullSubcategory

variable [Small.{u} I]

/-- The component algebraic spaces of a descent datum. -/
abbrev localSpace (D : DescentData Xᵢ f) (i : I) : AlgebraicSpace S :=
  (D.obj i).left

/-- The structure map of a component space to `X`. -/
abbrev localToX (D : DescentData Xᵢ f) (i : I) : localSpace Xᵢ f D i ⟶ X :=
  (D.obj i).hom ≫ f i

/-- The overlap algebraic space `Vᵢ ×_X Xⱼ`. -/
def overlapSpace (D : DescentData Xᵢ f) (i j : I) : AlgebraicSpace S :=
  pullbackOver (localToX Xᵢ f D i) (f j) X.isSheaf X.representableDiagonal

/-- The first projection `Vᵢ ×_X Xⱼ ⟶ Vᵢ`. -/
def overlapToLeft (D : DescentData Xᵢ f) (i j : I) :
    overlapSpace Xᵢ f D i j ⟶ localSpace Xᵢ f D i :=
  pullbackOverFst (localToX Xᵢ f D i) (f j) X.isSheaf X.representableDiagonal

/-- The second projection `Vᵢ ×_X Xⱼ ⟶ Xⱼ`. -/
def overlapToCover (D : DescentData Xᵢ f) (i j : I) :
    overlapSpace Xᵢ f D i j ⟶ Xᵢ j :=
  pullbackOverSnd (localToX Xᵢ f D i) (f j) X.isSheaf X.representableDiagonal

/-- The composite `Vᵢ ×_X Xⱼ ⟶ Xᵢ`. -/
def overlapToLocalCover (D : DescentData Xᵢ f) (i j : I) :
    overlapSpace Xᵢ f D i j ⟶ Xᵢ i :=
  overlapToLeft Xᵢ f D i j ≫ (D.obj i).hom

/-- The two projections of an overlap agree after mapping to `X`. -/
theorem overlapToCover_comp (D : DescentData Xᵢ f) (i j : I) :
    overlapToCover Xᵢ f D i j ≫ f j = overlapToLocalCover Xᵢ f D i j ≫ f i :=
  sorry

/-- The tautological section of `Vᵢ` over the overlap `Vᵢ ×_X Xⱼ`. -/
def overlapTaut (D : DescentData Xᵢ f) (i j : I) :
    overlapSpace Xᵢ f D i j ⟶
      ((overPullback (overlapToLocalCover Xᵢ f D i j)).obj (D.obj i)).left :=
  pullbackLift (D.obj i).hom (overlapToLocalCover Xᵢ f D i j)
    (overlapToLeft Xᵢ f D i j) (𝟙 (overlapSpace Xᵢ f D i j)) sorry

/-- The descent comparison on an overlap, followed by projection to `Vⱼ`. -/
def overlapToRight (D : DescentData Xᵢ f) (i j : I) :
    overlapSpace Xᵢ f D i j ⟶ localSpace Xᵢ f D j :=
  overlapTaut Xᵢ f D i j ≫
    (D.hom (overlapToLocalCover Xᵢ f D i j ≫ f i)
        (overlapToLocalCover Xᵢ f D i j) (overlapToCover Xᵢ f D i j) rfl
        (overlapToCover_comp Xᵢ f D i j)).left ≫
      overPullbackFst (overlapToCover Xᵢ f D i j) (D.obj j)

/-- The sheaf associated to the component space `Vᵢ`. -/
abbrev localSheaf (D : DescentData Xᵢ f) (i : I) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  toSheaf (localSpace Xᵢ f D i)

/-- The sheaf associated to an overlap `Vᵢ ×_X Xⱼ`. -/
abbrev overlapSheaf (D : DescentData Xᵢ f) (i j : I) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  toSheaf (overlapSpace Xᵢ f D i j)

/-- The small family of component spaces `Vᵢ`. -/
abbrev localFamily (D : DescentData Xᵢ f) : I → AlgebraicSpace S :=
  fun i ↦ localSpace Xᵢ f D i

/-- The small family of overlap spaces `Vᵢ ×_X Xⱼ`. -/
abbrev overlapFamily (D : DescentData Xᵢ f) : I × I → AlgebraicSpace S :=
  fun ij ↦ overlapSpace Xᵢ f D ij.1 ij.2

/-- The coproduct `∐ᵢ Vᵢ` of the component spaces of a descent datum. -/
def localCoproduct (D : DescentData Xᵢ f) : AlgebraicSpace S :=
  coproduct (localFamily Xᵢ f D)

/-- The coproduct of component spaces is `coproduct` of `localFamily`. -/
theorem localCoproduct_eq (D : DescentData Xᵢ f) :
    localCoproduct Xᵢ f D = coproduct (localFamily Xᵢ f D) :=
  rfl

/-- The coproduct `∐_{i,j} Vᵢ ×_X Xⱼ` of the overlap spaces of a descent datum. -/
def overlapCoproduct (D : DescentData Xᵢ f) : AlgebraicSpace S :=
  coproduct (overlapFamily Xᵢ f D)

/-- The first relation map `∐_{i,j} Vᵢ ×_X Xⱼ ⟶ ∐ᵢ Vᵢ`, induced by the projections
`Vᵢ ×_X Xⱼ ⟶ Vᵢ`. -/
def relationFstSpace (D : DescentData Xᵢ f) :
    overlapCoproduct Xᵢ f D ⟶ localCoproduct Xᵢ f D :=
  coproductDesc fun ij ↦
    overlapToLeft Xᵢ f D ij.1 ij.2 ≫ coproductι (localFamily Xᵢ f D) ij.1

/-- The second relation map `∐_{i,j} Vᵢ ×_X Xⱼ ⟶ ∐ᵢ Vᵢ`, induced by the descent
comparisons `φᵢⱼ` followed by projection to `Vⱼ`. -/
def relationSndSpace (D : DescentData Xᵢ f) :
    overlapCoproduct Xᵢ f D ⟶ localCoproduct Xᵢ f D :=
  coproductDesc fun ij ↦
    overlapToRight Xᵢ f D ij.1 ij.2 ≫ coproductι (localFamily Xᵢ f D) ij.2

/-- The first coproduct relation as a morphism of fppf sheaves. -/
def relationFst (D : DescentData Xᵢ f) :
    toSheaf (overlapCoproduct Xᵢ f D) ⟶ toSheaf (localCoproduct Xᵢ f D) :=
  toSheafMap (relationFstSpace Xᵢ f D)

/-- The second coproduct relation as a morphism of fppf sheaves. -/
def relationSnd (D : DescentData Xᵢ f) :
    toSheaf (overlapCoproduct Xᵢ f D) ⟶ toSheaf (localCoproduct Xᵢ f D) :=
  toSheafMap (relationSndSpace Xᵢ f D)

/-- The underlying presheaf morphism of `relationFst` is `relationFstSpace`. -/
theorem relationFst_hom (D : DescentData Xᵢ f) :
    (relationFst Xᵢ f D).hom = relationFstSpace Xᵢ f D :=
  rfl

/-- The underlying presheaf morphism of `relationSnd` is `relationSndSpace`. -/
theorem relationSnd_hom (D : DescentData Xᵢ f) :
    (relationSnd Xᵢ f D).hom = relationSndSpace Xᵢ f D :=
  rfl

/-- The presheaf coequalizer of `∐_{i,j} toSheaf(Vᵢ ×_X Xⱼ) ⇉ ∐ᵢ toSheaf Vᵢ`. -/
def gluedPresheaf (D : DescentData Xᵢ f) : (Over S)ᵒᵖ ⥤ Type u :=
  coequalizer
    (relationFst Xᵢ f D).hom
    (relationSnd Xᵢ f D).hom

/-- The sheaf on `(Sch/S)_fppf` glued from descent data: the Type `u` sheafification of
the coproduct coequalizer `∐_{i,j} toSheaf(Vᵢ ×_X Xⱼ) ⇉ ∐ᵢ toSheaf Vᵢ`. -/
def gluedSheaf (D : DescentData Xᵢ f) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨sheafifyTypeU (gluedPresheaf Xᵢ f D), sheafifyTypeU_isSheaf _⟩

/-- The underlying presheaf of `gluedSheaf D` is the Type `u` sheafification of the
coproduct coequalizer. -/
theorem gluedSheaf_obj (D : DescentData Xᵢ f) :
    (gluedSheaf Xᵢ f D).obj = sheafifyTypeU (gluedPresheaf Xᵢ f D) :=
  rfl

/-- The two overlap maps coequalize after the coproduct inclusions into `X`. -/
theorem relation_comp_toX (D : DescentData Xᵢ f) :
    (relationFst Xᵢ f D).hom ≫ coproductDesc (localToX Xᵢ f D) =
      (relationSnd Xᵢ f D).hom ≫ coproductDesc (localToX Xᵢ f D) :=
  sorry

/-- The presheaf comparison from the coproduct coequalizer to `toSheaf X`. -/
def gluedToXPresheaf (D : DescentData Xᵢ f) :
    gluedPresheaf Xᵢ f D ⟶ X.functorOfPoints :=
  coequalizer.desc (coproductDesc (localToX Xᵢ f D)) (relation_comp_toX Xᵢ f D)

/-- The structure map of the glued sheaf to `toSheaf X`. -/
def gluedToX (D : DescentData Xᵢ f) : gluedSheaf Xᵢ f D ⟶ toSheaf X :=
  ObjectProperty.homMk (sheafifyTypeULift (gluedToXPresheaf Xᵢ f D) X.isSheaf)

/-- A morphism of descent data induces maps of component spaces. -/
def localMap {D E : DescentData Xᵢ f} (φ : D ⟶ E) (i : I) :
    localSpace Xᵢ f D i ⟶ localSpace Xᵢ f E i :=
  (φ.hom i).left

/-- The coproduct of the component maps of a morphism of descent data. -/
def localCoproductMap {D E : DescentData Xᵢ f} (φ : D ⟶ E) :
    localCoproduct Xᵢ f D ⟶ localCoproduct Xᵢ f E :=
  coproductDesc fun i ↦ localMap Xᵢ f φ i ≫ coproductι (localFamily Xᵢ f E) i

/-- The coproduct of the local maps coequalizes the two overlap relations. -/
theorem localCoproductMap_coequalizes {D E : DescentData Xᵢ f} (φ : D ⟶ E) :
    (relationFst Xᵢ f D).hom ≫ localCoproductMap Xᵢ f φ ≫
        coequalizer.π (relationFst Xᵢ f E).hom (relationSnd Xᵢ f E).hom =
      (relationSnd Xᵢ f D).hom ≫ localCoproductMap Xᵢ f φ ≫
        coequalizer.π (relationFst Xᵢ f E).hom (relationSnd Xᵢ f E).hom :=
  sorry

/-- The morphism of coequalizer presheaves induced by a morphism of descent data. -/
def gluedPresheafMap {D E : DescentData Xᵢ f} (φ : D ⟶ E) :
    gluedPresheaf Xᵢ f D ⟶ gluedPresheaf Xᵢ f E :=
  coequalizer.desc
    (localCoproductMap Xᵢ f φ ≫
      coequalizer.π (relationFst Xᵢ f E).hom (relationSnd Xᵢ f E).hom)
    (localCoproductMap_coequalizes Xᵢ f φ)

/-- The morphism of glued sheaves induced by a morphism of descent data. -/
def gluedMap {D E : DescentData Xᵢ f} (φ : D ⟶ E) :
    gluedSheaf Xᵢ f D ⟶ gluedSheaf Xᵢ f E :=
  ObjectProperty.homMk
    (plusTypeUMap (plusTypeUMap (gluedPresheafMap Xᵢ f φ)))

/-- The glued map of an identity descent morphism is the identity. -/
theorem gluedMap_id (D : DescentData Xᵢ f) :
    gluedMap Xᵢ f (𝟙 D) = 𝟙 (gluedSheaf Xᵢ f D) :=
  sorry

/-- Glued maps preserve composition of descent morphisms. -/
theorem gluedMap_comp {D E F : DescentData Xᵢ f} (φ : D ⟶ E) (ψ : E ⟶ F) :
    gluedMap Xᵢ f (φ ≫ ψ) = gluedMap Xᵢ f φ ≫ gluedMap Xᵢ f ψ :=
  sorry

/-- The glued sheaf of a descent morphism lies over `toSheaf X`. -/
theorem gluedMap_over {D E : DescentData Xᵢ f} (φ : D ⟶ E) :
    gluedMap Xᵢ f φ ≫ gluedToX Xᵢ f E = gluedToX Xᵢ f D :=
  sorry

/-- The inclusion of a component space into the glued sheaf, as the coproduct inclusion
followed by the coequalizer projection and sheafification unit. -/
def localToGlued (D : DescentData Xᵢ f) (i : I) :
    toSheaf (localSpace Xᵢ f D i) ⟶ gluedSheaf Xᵢ f D :=
  ObjectProperty.homMk <|
    coproductι (localFamily Xᵢ f D) i ≫
      coequalizer.π (relationFst Xᵢ f D).hom (relationSnd Xᵢ f D).hom ≫
        toSheafifyTypeU (gluedPresheaf Xᵢ f D)

/-- The inclusion of a component space into the glued sheaf is compatible with the
maps to `X`. -/
theorem localToGlued_comp (D : DescentData Xᵢ f) (i : I) :
    toSheafMap (localToX Xᵢ f D i) = localToGlued Xᵢ f D i ≫ gluedToX Xᵢ f D :=
  sorry

/-- The two overlap maps coequalize after inclusion into the glued sheaf. -/
theorem relation_comp_localToGlued (D : DescentData Xᵢ f) (i j : I) :
    toSheafMap (overlapToLeft Xᵢ f D i j) ≫ localToGlued Xᵢ f D i =
      toSheafMap (overlapToRight Xᵢ f D i j) ≫ localToGlued Xᵢ f D j :=
  sorry

variable [FppfCovering Xᵢ f]

/-- The glued sheaf of descent data is locally an algebraic space along the covering
family. -/
theorem gluedSheaf_locallyAlgebraic (D : DescentData Xᵢ f) :
    locallyAlgebraicSpaceAlong Xᵢ f (Over.mk (gluedToX Xᵢ f D)) :=
  sorry

/-- Explicit gluing sends algebraic-space descent data to sheaves over `X` whose
pullbacks along the covering family are algebraic spaces. -/
def glue : DescentData Xᵢ f ⥤ LocallyAlgebraicSpaceAlong Xᵢ f where
  obj D := ⟨Over.mk (gluedToX Xᵢ f D), gluedSheaf_locallyAlgebraic Xᵢ f D⟩
  map φ := ObjectProperty.homMk (Over.homMk (gluedMap Xᵢ f φ) (gluedMap_over Xᵢ f φ))
  map_id := sorry
  map_comp := sorry

/-- The underlying object of `glue.obj D` is the glued sheaf over `toSheaf X`. -/
theorem glue_obj (D : DescentData Xᵢ f) :
    ((glue Xᵢ f).obj D).obj = Over.mk (gluedToX Xᵢ f D) :=
  rfl

/-- The sheaf fibre product `Xᵢ ×_X F` is an algebraic space. -/
instance instIsAlgebraicSpace_sheafFiber (F : LocallyAlgebraicSpaceAlong Xᵢ f) (i : I) :
    IsAlgebraicSpace (pullback (toSheafMap (f i)) F.obj.hom).obj :=
  F.property i

/-- The algebraic space `Xᵢ ×_X F` associated to a sheaf over `X` whose pullbacks along
the covering family are algebraic spaces. -/
def sheafFiber (F : LocallyAlgebraicSpaceAlong Xᵢ f) (i : I) : AlgebraicSpace S :=
  ofIsAlgebraicSpace (pullback (toSheafMap (f i)) F.obj.hom).obj

/-- The structure morphism `Xᵢ ×_X F ⟶ Xᵢ` is the first projection of the sheaf
fibre product. -/
def fiberToCover (F : LocallyAlgebraicSpaceAlong Xᵢ f) (i : I) :
    sheafFiber Xᵢ f F i ⟶ Xᵢ i :=
  (pullback.fst (toSheafMap (f i)) F.obj.hom).hom

/-- The structure map `sheafFiber F i ⟶ Xᵢ` is the first sheaf projection. -/
theorem sheafFiber_fst (F : LocallyAlgebraicSpaceAlong Xᵢ f) (i : I) :
    fiberToCover Xᵢ f F i = (pullback.fst (toSheafMap (f i)) F.obj.hom).hom :=
  rfl

/-- The structure morphism `Xᵢ ×_X F ⟶ F` is the second projection of the sheaf
fibre product. -/
def fiberToSheaf (F : LocallyAlgebraicSpaceAlong Xᵢ f) (i : I) :
    toSheaf (sheafFiber Xᵢ f F i) ⟶ F.obj.left :=
  ObjectProperty.homMk (pullback.snd (toSheafMap (f i)) F.obj.hom).hom

/-- The two projections of `Xᵢ ×_X F` agree after mapping to `X`. -/
theorem fiber_comp (F : LocallyAlgebraicSpaceAlong Xᵢ f) (i : I) :
    toSheafMap (fiberToCover Xᵢ f F i) ≫ toSheafMap (f i) =
      fiberToSheaf Xᵢ f F i ≫ F.obj.hom :=
  sorry

/-- The left component of a descent comparison between fibre products of a sheaf along
two maps into the covering family. -/
def fromSheafHomLeft {Y : AlgebraicSpace S} (F : LocallyAlgebraicSpaceAlong Xᵢ f)
    {i₁ i₂ : I} (f₁ : Y ⟶ Xᵢ i₁) (f₂ : Y ⟶ Xᵢ i₂) :
    ((overPullback f₁).obj (Over.mk (fiberToCover Xᵢ f F i₁))).left ⟶
      ((overPullback f₂).obj (Over.mk (fiberToCover Xᵢ f F i₂))).left :=
  pullbackLift (fiberToCover Xᵢ f F i₂) f₂
    ((pullback.lift
        (toSheafMap (overPullbackSnd f₁ (Over.mk (fiberToCover Xᵢ f F i₁)) ≫ f₂))
        (toSheafMap (overPullbackFst f₁ (Over.mk (fiberToCover Xᵢ f F i₁))) ≫
          fiberToSheaf Xᵢ f F i₁)
        sorry).hom)
    (overPullbackSnd f₁ (Over.mk (fiberToCover Xᵢ f F i₁)))
    sorry

/-- Descent comparisons between fibre products of a sheaf lie over the test object. -/
theorem fromSheafHom_fac {Y : AlgebraicSpace S} (F : LocallyAlgebraicSpaceAlong Xᵢ f)
    {i₁ i₂ : I} (f₁ : Y ⟶ Xᵢ i₁) (f₂ : Y ⟶ Xᵢ i₂) :
    fromSheafHomLeft Xᵢ f F f₁ f₂ ≫
        overPullbackSnd f₂ (Over.mk (fiberToCover Xᵢ f F i₂)) =
      overPullbackSnd f₁ (Over.mk (fiberToCover Xᵢ f F i₁)) :=
  sorry

/-- The descent comparison between fibre products of a sheaf, as a morphism over the
test algebraic space. -/
def fromSheafHom {Y : AlgebraicSpace S} (F : LocallyAlgebraicSpaceAlong Xᵢ f)
    (q : Y ⟶ X) {i₁ i₂ : I} (f₁ : Y ⟶ Xᵢ i₁) (f₂ : Y ⟶ Xᵢ i₂)
    (_ : f₁ ≫ f i₁ = q) (_ : f₂ ≫ f i₂ = q) :
    (overPullback f₁).obj (Over.mk (fiberToCover Xᵢ f F i₁)) ⟶
      (overPullback f₂).obj (Over.mk (fiberToCover Xᵢ f F i₂)) :=
  Over.homMk (fromSheafHomLeft Xᵢ f F f₁ f₂) (fromSheafHom_fac Xᵢ f F f₁ f₂)

/-- Restricting a sheaf over `X` along the covering family produces algebraic-space
descent data. -/
def fromSheafObj (F : LocallyAlgebraicSpaceAlong Xᵢ f) : DescentData Xᵢ f where
  obj i := Over.mk (fiberToCover Xᵢ f F i)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := fromSheafHom Xᵢ f F q f₁ f₂ hf₁ hf₂
  pullHom_hom := sorry
  hom_self := sorry
  hom_comp := sorry

/-- The `i`th component of `fromSheafObj F` is `Xᵢ ×_X F` over `Xᵢ`. -/
theorem fromSheaf_obj_obj (F : LocallyAlgebraicSpaceAlong Xᵢ f) (i : I) :
    (fromSheafObj Xᵢ f F).obj i = Over.mk (fiberToCover Xᵢ f F i) :=
  rfl

/-- A morphism of sheaves over `X` induces a morphism of fibre products along a covering
member. -/
def fiberMap {F G : LocallyAlgebraicSpaceAlong Xᵢ f} (ψ : F ⟶ G) (i : I) :
    sheafFiber Xᵢ f F i ⟶ sheafFiber Xᵢ f G i :=
  (pullback.map (toSheafMap (f i)) F.obj.hom (toSheafMap (f i)) G.obj.hom
      (𝟙 (toSheaf (Xᵢ i))) ψ.hom.left (𝟙 (toSheaf X)) sorry sorry).hom

/-- Fibre maps induced by a morphism of sheaves over `X` lie over `Xᵢ`. -/
theorem fiberMap_cover {F G : LocallyAlgebraicSpaceAlong Xᵢ f} (ψ : F ⟶ G) (i : I) :
    fiberMap Xᵢ f ψ i ≫ fiberToCover Xᵢ f G i = fiberToCover Xᵢ f F i :=
  sorry

/-- A morphism of sheaves over `X` induces a morphism of the associated descent data. -/
def fromSheafMap {F G : LocallyAlgebraicSpaceAlong Xᵢ f} (ψ : F ⟶ G) :
    fromSheafObj Xᵢ f F ⟶ fromSheafObj Xᵢ f G where
  hom i := Over.homMk (fiberMap Xᵢ f ψ i) (fiberMap_cover Xᵢ f ψ i)
  comm := sorry

/-- Restricting sheaves over `X` along the covering family is a functor to descent
data. -/
def fromSheaf : LocallyAlgebraicSpaceAlong Xᵢ f ⥤ DescentData Xᵢ f where
  obj := fromSheafObj Xᵢ f
  map ψ := fromSheafMap Xᵢ f ψ
  map_id := sorry
  map_comp := sorry

/-- The glued sheaf corepresents compatible families for the overlap coequalizer
diagram of local and overlap sheaves. -/
theorem isCoequalizer (D : DescentData Xᵢ f)
    {G : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (π : ∀ i, localSheaf Xᵢ f D i ⟶ G)
    (_hπ : ∀ i j,
      toSheafMap (overlapToLeft Xᵢ f D i j) ≫ π i =
        toSheafMap (overlapToRight Xᵢ f D i j) ≫ π j) :
    ∃! (α : gluedSheaf Xᵢ f D ⟶ G), ∀ i, localToGlued Xᵢ f D i ≫ α = π i :=
  sorry

/-- The canonical comparison `Vᵢ ⟶ Xᵢ ×_X F` from a component of descent data into the
corresponding fibre of the glued sheaf. -/
def productComparisonInvLeft (D : DescentData Xᵢ f) (i : I) :
    localSpace Xᵢ f D i ⟶ sheafFiber Xᵢ f ((glue Xᵢ f).obj D) i :=
  (pullback.lift (toSheafMap (D.obj i).hom) (localToGlued Xᵢ f D i) sorry).hom

/-- The comparison `Vᵢ ⟶ Xᵢ ×_X F` lies over `Xᵢ`. -/
theorem productComparisonInvLeft_cover (D : DescentData Xᵢ f) (i : I) :
    productComparisonInvLeft Xᵢ f D i ≫
        fiberToCover Xᵢ f ((glue Xᵢ f).obj D) i = (D.obj i).hom :=
  sorry

/-- The coequalizer-inclusion comparison `Vᵢ ⟶ Xᵢ ×_X gluedSheaf` is an isomorphism. -/
instance instIsIso_productComparisonInvLeft (D : DescentData Xᵢ f) (i : I) :
    IsIso (productComparisonInvLeft Xᵢ f D i) :=
  sorry

/-- The comparison `Xᵢ ×_X F ⟶ Vᵢ` is the inverse of the coequalizer inclusion. -/
def productComparisonHomLeft (D : DescentData Xᵢ f) (i : I) :
    sheafFiber Xᵢ f ((glue Xᵢ f).obj D) i ⟶ localSpace Xᵢ f D i :=
  CategoryTheory.inv (productComparisonInvLeft Xᵢ f D i)

/-- The comparison `Xᵢ ×_X F ⟶ Vᵢ` lies over `Xᵢ`. -/
theorem productComparisonHomLeft_cover (D : DescentData Xᵢ f) (i : I) :
    productComparisonHomLeft Xᵢ f D i ≫ (D.obj i).hom =
      fiberToCover Xᵢ f ((glue Xᵢ f).obj D) i :=
  sorry

/-- The comparison identifying `Vᵢ` with `Xᵢ ×_X F`, as an isomorphism over `Xᵢ`. -/
def productIso (D : DescentData Xᵢ f) (i : I) :
    D.obj i ≅ ((fromSheaf Xᵢ f).obj ((glue Xᵢ f).obj D)).obj i :=
  Over.isoMk
    { hom := productComparisonInvLeft Xᵢ f D i
      inv := productComparisonHomLeft Xᵢ f D i
      hom_inv_id := sorry
      inv_hom_id := sorry }
    (productComparisonInvLeft_cover Xᵢ f D i)

/-- The forward map of `productIso` is the coequalizer inclusion of the component
space into the fibre product. -/
theorem productIso_hom (D : DescentData Xᵢ f) (i : I) :
    (productIso Xᵢ f D i).hom =
      Over.homMk (productComparisonInvLeft Xᵢ f D i)
        (productComparisonInvLeft_cover Xᵢ f D i) :=
  sorry

/-- The inverse map of `productIso` is the inverse of the coequalizer inclusion. -/
theorem productIso_inv (D : DescentData Xᵢ f) (i : I) :
    (productIso Xᵢ f D i).inv =
      Over.homMk (productComparisonHomLeft Xᵢ f D i)
        (productComparisonHomLeft_cover Xᵢ f D i) :=
  sorry

/-- The morphism `toSheaf (coproduct G) ⟶ P` induced by a family of morphisms from the
summands into a sheaf. -/
def coproductToSheafDesc {G : I → AlgebraicSpace S}
    {P : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (p : ∀ i, toSheaf (G i) ⟶ P) :
    toSheaf (coproduct G) ⟶ P :=
  ObjectProperty.homMk
    { app T := ↾fun s ↦
        (P.property.amalgamateOfArrows
            (fun i : Shrink.{u} I ↦ Over.homMk (s.piece i).ι rfl)
            (CoproductSection.ofArrows_mem s)
            (fun i ↦ ↾fun (_ : PUnit.{u + 1}) ↦
              (p ((equivShrink.{u} I).symm i)).hom.app
                (op (Over.mk ((s.piece i).ι ≫ (unop T).hom)))
                (s.summandSection i))
            sorry)
          PUnit.unit
      naturality := sorry }

/-- Postcomposing a coproduct inclusion with `coproductToSheafDesc p` recovers `p`. -/
theorem coproductToSheafDesc_comp {G : I → AlgebraicSpace S}
    {P : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (p : ∀ i, toSheaf (G i) ⟶ P) (i : I) :
    toSheafMap (coproductι G i) ≫ coproductToSheafDesc p = p i :=
  sorry

/-- The coproduct of the restricted fibres `Xᵢ ×_X F` maps to `F` by the second
projections. -/
def sheafCounitFromCoproduct (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    toSheaf (localCoproduct Xᵢ f ((fromSheaf Xᵢ f).obj F)) ⟶ F.obj.left :=
  coproductToSheafDesc (fun i ↦ fiberToSheaf Xᵢ f F i)

/-- The family of restricted sheaves `Xᵢ ×_X F` coequalizes after mapping to `F`. -/
theorem fiberToSheaf_coequalizes (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    (relationFst Xᵢ f ((fromSheaf Xᵢ f).obj F)).hom ≫
        (sheafCounitFromCoproduct Xᵢ f F).hom =
      (relationSnd Xᵢ f ((fromSheaf Xᵢ f).obj F)).hom ≫
        (sheafCounitFromCoproduct Xᵢ f F).hom :=
  sorry

/-- The presheaf comparison from the coequalizer of restricted descent data to `F`. -/
def sheafCounitPresheaf (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    gluedPresheaf Xᵢ f ((fromSheaf Xᵢ f).obj F) ⟶ F.obj.left.obj :=
  coequalizer.desc (sheafCounitFromCoproduct Xᵢ f F).hom
    (fiberToSheaf_coequalizes Xᵢ f F)

/-- The coequalizer comparison from the glued sheaf of a restricted sheaf to the original
sheaf. -/
def sheafCounitHomLeft (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    gluedSheaf Xᵢ f ((fromSheaf Xᵢ f).obj F) ⟶ F.obj.left :=
  ObjectProperty.homMk (sheafifyTypeULift (sheafCounitPresheaf Xᵢ f F) F.obj.left.property)

/-- The coequalizer comparison of a restricted sheaf lies over `toSheaf X`. -/
theorem sheafCounitHomLeft_over (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    sheafCounitHomLeft Xᵢ f F ≫ F.obj.hom =
      gluedToX Xᵢ f ((fromSheaf Xᵢ f).obj F) :=
  sorry

/-- The counit component as a morphism of sheaves over `X`. -/
def sheafCounitHom (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    (glue Xᵢ f).obj ((fromSheaf Xᵢ f).obj F) ⟶ F :=
  ObjectProperty.homMk
    (Over.homMk (sheafCounitHomLeft Xᵢ f F) (sheafCounitHomLeft_over Xᵢ f F))

/-- The left map of `sheafCounitHom` is the coequalizer comparison. -/
theorem sheafCounitHom_left (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    (sheafCounitHom Xᵢ f F).hom.left = sheafCounitHomLeft Xᵢ f F :=
  rfl

/-- The coequalizer comparison reconstructing a sheaf from its restricted descent data is
an isomorphism. -/
instance instIsIso_sheafCounitHomLeft (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    IsIso (sheafCounitHomLeft Xᵢ f F) :=
  sorry

/-- The inverse comparison reconstructing a sheaf from the sheaf coequalizer of its
restricted descent data. -/
def sheafCounitInvLeft (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    F.obj.left ⟶ gluedSheaf Xᵢ f ((fromSheaf Xᵢ f).obj F) :=
  CategoryTheory.inv (sheafCounitHomLeft Xᵢ f F)

/-- The inverse counit component reconstructing a sheaf from its restricted descent data. -/
theorem sheafCounitInvLeft_over (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    sheafCounitInvLeft Xᵢ f F ≫ gluedToX Xᵢ f ((fromSheaf Xᵢ f).obj F) =
      F.obj.hom :=
  sorry

/-- The inverse counit component as a morphism of sheaves over `X`. -/
def sheafCounitInv (F : LocallyAlgebraicSpaceAlong Xᵢ f) :
    F ⟶ (glue Xᵢ f).obj ((fromSheaf Xᵢ f).obj F) :=
  ObjectProperty.homMk
    (Over.homMk (sheafCounitInvLeft Xᵢ f F) (sheafCounitInvLeft_over Xᵢ f F))

/-- The unit component sending descent data to the descent data of its glued sheaf. -/
def sheafUnitHom (D : DescentData Xᵢ f) :
    D ⟶ (fromSheaf Xᵢ f).obj ((glue Xᵢ f).obj D) where
  hom i := (productIso Xᵢ f D i).hom
  comm := sorry

/-- The inverse unit component recovering descent data from the glued sheaf. -/
def sheafUnitInv (D : DescentData Xᵢ f) :
    (fromSheaf Xᵢ f).obj ((glue Xᵢ f).obj D) ⟶ D where
  hom i := (productIso Xᵢ f D i).inv
  comm := sorry

/-- The unit isomorphism of algebraic-space sheaf descent. -/
def sheafUnitIso :
    𝟭 (DescentData Xᵢ f) ≅ glue Xᵢ f ⋙ fromSheaf Xᵢ f :=
  NatIso.ofComponents
    (fun D ↦
      { hom := sheafUnitHom Xᵢ f D
        inv := sheafUnitInv Xᵢ f D
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The counit isomorphism of algebraic-space sheaf descent. -/
def sheafCounitIso :
    fromSheaf Xᵢ f ⋙ glue Xᵢ f ≅ 𝟭 (LocallyAlgebraicSpaceAlong Xᵢ f) :=
  NatIso.ofComponents
    (fun F ↦
      { hom := sheafCounitHom Xᵢ f F
        inv := sheafCounitInv Xᵢ f F
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Descent data relative to an fppf covering of algebraic spaces are equivalent to
sheaves on `(Sch/S)_fppf` over `X` whose pullbacks along the covering are algebraic
spaces. -/
def sheafEquivalence : DescentData Xᵢ f ≌ LocallyAlgebraicSpaceAlong Xᵢ f :=
  CategoryTheory.Equivalence.mk (glue Xᵢ f) (fromSheaf Xᵢ f)
    (sheafUnitIso Xᵢ f) (sheafCounitIso Xᵢ f)

/-- The forward functor of `sheafEquivalence` is gluing of descent data. -/
theorem sheafEquivalence_functor :
    (sheafEquivalence Xᵢ f).functor = glue Xᵢ f :=
  rfl

/-- The inverse functor of `sheafEquivalence` restricts sheaves along the covering. -/
theorem sheafEquivalence_inverse :
    (sheafEquivalence Xᵢ f).inverse = fromSheaf Xᵢ f :=
  rfl

/-- Gluing of algebraic-space descent data along an fppf covering is an equivalence. -/
instance glueIsEquivalence : (glue Xᵢ f).IsEquivalence :=
  sorry

/-- The sheaf glued from a descent datum is an algebraic space if and only if the
descent datum is effective. -/
theorem isAlgebraicSpace_iff_effective (D : DescentData Xᵢ f) :
    IsAlgebraicSpace (gluedSheaf Xᵢ f D).obj ↔ D.IsEffective :=
  sorry

end DescentData

end AlgebraicGeometry.AlgebraicSpace
