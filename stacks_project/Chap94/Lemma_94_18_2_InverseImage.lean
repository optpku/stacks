module

public import Mathlib.CategoryTheory.EssentiallySmall
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.Cartesian.MapHom
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Existence
public import stacks_project.Chap78.Lemma_78_28_1_Comparison
public import stacks_project.Chap94.Definition_94_12_3_AlgebraicStacks
public import stacks_project.Chap94.Lemma_94_18_1
public import stacks_project.Chap94.Lemma_94_18_2_OnSlice

/-!
# Inverse image of algebraic stacks along an enlargement of big sites

The rule `X ↦ f⁻¹X` of Lemma 94.18.1, applied to algebraic stacks defined using a
contained site `(C, J)`, yields algebraic stacks on the large fppf site of `ι.obj S`.
The induced Hom-functors are equivalences, and the essential image consists of those
large-site algebraic stacks that admit a presentation `[U' / R']` with `U', R'`
isomorphic to the inverse images of algebraic spaces on the contained site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits
open scoped Bicategory

noncomputable section

universe u uC w

namespace AlgebraicGeometry.AlgebraicStacksOnSlice

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [(slicePost ι S).IsCocontinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]
variable [HasPullbacks (Over S)] [HasEqualizers (Over S)]
variable [PreservesLimitsOfShape WalkingCospan (slicePost ι S)]
variable [PreservesLimitsOfShape WalkingParallelPair (slicePost ι S)]
variable [Small.{w} (Over (ι.obj S))]

/-- The selected inverse-image stack of the underlying stack in groupoids of a
contained-site algebraic stack. -/
def inverseImage.canonical (X : AlgebraicStacksOnSlice ι J S) :
    StackOver.InverseImage (Scheme.fppfTopology.over (ι.obj S)) (slicePost ι S)
      (toStackOver ι J S X) :=
  StackOver.InverseImage.canonical (K := Scheme.fppfTopology.over (ι.obj S))
    (slicePost ι S)

/-- The selected inverse-image target is a stack in groupoids on the large fppf site. -/
theorem inverseImage.target_isStackInGroupoids (X : AlgebraicStacksOnSlice ι J S) :
    IsStack.InGroupoids (Scheme.fppfTopology.over (ι.obj S))
      (inverseImage.canonical ι J S X).target.p := sorry

/-- The selected inverse-image stack, packaged as a stack in groupoids on the
large fppf site from the canonical inverse-image projection. -/
def inverseImage.asGroupoids (X : AlgebraicStacksOnSlice ι J S) :
    StackOver.Groupoids (Scheme.fppfTopology.over (ι.obj S)) :=
  StackOver.Groupoids.ofProjectionWith
    (Scheme.fppfTopology.over (ι.obj S))
    (inverseImage.canonical ι J S X).target.p
    (inverseImage.target_isStackInGroupoids ι J S X)

/-- The total category of the selected inverse-image stack is small in the universe
of `GroupoidsOver`. -/
instance inverseImage.totalSmall (X : AlgebraicStacksOnSlice ι J S) :
    Small.{u + 1} (inverseImage.canonical ι J S X).target.total :=
  sorry

/-- The object-universe shrinking of the selected inverse-image total category. -/
abbrev inverseImage.SmallTotal (X : AlgebraicStacksOnSlice ι J S) : Type (u + 1) :=
  Shrink.{u + 1} (inverseImage.canonical ι J S X).target.total

/-- Hom-sets of the object-universe shrinking are `u`-small. -/
instance inverseImage.smallTotalLocallySmall (X : AlgebraicStacksOnSlice ι J S) :
    LocallySmall.{u} (inverseImage.SmallTotal ι J S X) :=
  sorry

/-- The universe-pinned total category of the selected inverse-image stack. -/
abbrev inverseImage.PinnedTotal (X : AlgebraicStacksOnSlice ι J S) : Type (u + 1) :=
  ShrinkHoms (inverseImage.SmallTotal ι J S X)

/-- The universe-pinned projection of the selected inverse-image stack, over
`(Sch' / S)_fppf`. -/
def inverseImage.universeBridgeFunctor (X : AlgebraicStacksOnSlice ι J S) :
    inverseImage.PinnedTotal ι J S X ⥤ Over (ι.obj S) :=
  ShrinkHoms.inverse (C := inverseImage.SmallTotal ι J S X) ⋙
    (Shrink.equivalence (C := (inverseImage.canonical ι J S X).target.total)).inverse ⋙
    (inverseImage.canonical ι J S X).target.p

/-- The universe-pinned projection remains fibred in groupoids. -/
instance inverseImage.universeBridgeFunctor_isFiberedInGroupoids
    (X : AlgebraicStacksOnSlice ι J S) :
    Functor.IsFibered.InGroupoids (inverseImage.universeBridgeFunctor ι J S X) :=
  sorry

/-- Forget the selected inverse-image stack to a category fibred in groupoids over
`(Sch' / S)_fppf`, at the universe levels of `GroupoidsOver`. -/
def inverseImage.toGroupoidsOver (X : AlgebraicStacksOnSlice ι J S) :
    GroupoidsOver (ι.obj S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u}
    (inverseImage.universeBridgeFunctor ι J S X)

/-- Inverse image of a contained-site algebraic stack is algebraic on the large
fppf site. -/
instance inverseImage.instAlgebraicStack (X : AlgebraicStacksOnSlice ι J S) :
    AlgebraicStack (inverseImage.toGroupoidsOver ι J S X) :=
  sorry

/-- Inverse image of a contained-site algebraic stack along the morphism of sites
associated to `slicePost ι S`, packaged as an algebraic stack on the large fppf
site. -/
def inverseImage (X : AlgebraicStacksOnSlice ι J S) :
    AlgebraicStacks (ι.obj S) :=
  AlgebraicStacks.of (inverseImage.toGroupoidsOver ι J S X)

/-- The underlying groupoid fibration of `inverseImage X` is the universe-pinned
selected inverse-image stack. -/
theorem inverseImage.spec (X : AlgebraicStacksOnSlice ι J S) :
    AlgebraicStacks.toGroupoids (inverseImage ι J S X) =
      inverseImage.toGroupoidsOver ι J S X := sorry

/-- The projection of the packaged inverse image is the universe-pinned selected
inverse-image projection. -/
theorem inverseImage.toGroupoidsOver_p (X : AlgebraicStacksOnSlice ι J S) :
    (inverseImage.toGroupoidsOver ι J S X).p =
      inverseImage.universeBridgeFunctor ι J S X := sorry

/-- The comparison from the selected inverse-image projection to its
universe-pinned `GroupoidsOver` model. -/
def inverseImage.universeBridge (X : AlgebraicStacksOnSlice ι J S) :
    CartesianBasedFunctor
      (inverseImage.canonical ι J S X).target.p
      (inverseImage.toGroupoidsOver ι J S X).p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor
      ((Shrink.equivalence
          (C := (inverseImage.canonical ι J S X).target.total)).functor ⋙
        ShrinkHoms.functor (C := inverseImage.SmallTotal ι J S X))
      sorry)
    sorry

/-- The comparison from the universe-pinned `GroupoidsOver` model back to the
selected inverse-image projection. -/
def inverseImage.universeBridgeInv (X : AlgebraicStacksOnSlice ι J S) :
    CartesianBasedFunctor
      (inverseImage.toGroupoidsOver ι J S X).p
      (inverseImage.canonical ι J S X).target.p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor
      (ShrinkHoms.inverse (C := inverseImage.SmallTotal ι J S X) ⋙
        (Shrink.equivalence
          (C := (inverseImage.canonical ι J S X).target.total)).inverse)
      sorry)
    sorry

/-- The large-site algebraic stack `[f⁻¹U / f⁻¹R]` associated to a contained-site
groupoid presentation. -/
def inverseImage.ofPresentation (G : GroupoidOnSlice ι J S)
    [GroupoidAlgebraicSpace.Smooth G.inverseImage] :
    AlgebraicStacks (ι.obj S) :=
  AlgebraicStacks.of G.inverseImage.quotientStack

/-- Inverse image of the small-site quotient `[U / R]` compares to `[f⁻¹U / f⁻¹R]`
by the cartesian functor `quotientStackInverseImageHom` of Lemma 78.28.1. -/
def inverseImage.ofPresentation_equiv (G : GroupoidOnSlice ι J S)
    [GroupoidAlgebraicSpace.Smooth G.inverseImage] :
    CartesianBasedFunctor
      (inverseImage.canonical ι J S (of ι J S (sliceQuotientStack ι J S G))).target.p
      (fppfQuotientStack G.inverseImage).p :=
  quotientStackInverseImageHom ι J S G

/-- The comparison `f⁻¹[U / R] ⟶ [f⁻¹U / f⁻¹R]` is the cartesian functor of
Lemma 78.28.1. -/
theorem inverseImage.ofPresentation_equiv_eq (G : GroupoidOnSlice ι J S)
    [GroupoidAlgebraicSpace.Smooth G.inverseImage] :
    inverseImage.ofPresentation_equiv ι J S G =
      quotientStackInverseImageHom ι J S G := sorry

/-- The Lemma 78.28.1 comparison target `[f⁻¹U / f⁻¹R]` is equivalent to the
quotient stack of the inverse-image groupoid. -/
theorem inverseImage.fppfQuotientStack_equiv_quotientStack
    (G : GroupoidOnSlice ι J S) :
    Nonempty
      (CartesianBasedFunctor
        (fppfQuotientStack G.inverseImage).p
        (G.inverseImage.quotientStack).p) := sorry

/-- The comparison `f⁻¹[U / R] ⟶ [f⁻¹U / f⁻¹R]` is an equivalence over the large
fppf site. -/
instance inverseImage.ofPresentation_equiv.isEquivalence (G : GroupoidOnSlice ι J S)
    [GroupoidAlgebraicSpace.Smooth G.inverseImage] :
    (inverseImage.ofPresentation_equiv ι J S G).toBasedFunctor.IsEquivalence :=
  sorry

/-- Forget a morphism of contained-site algebraic stacks to a cartesian functor of
underlying stacks. -/
def inverseImage.toCartesianFunctor (X Y : AlgebraicStacksOnSlice ι J S) :
    (X ⟶ Y) ⥤
      CartesianBasedFunctor (toStackOver ι J S X).p (toStackOver ι J S Y).p where
  obj f := StackOver.Groupoids.Hom.toCartesianBasedFunctor f.hom
  map η :=
    CartesianBasedFunctor.homMk
      (FiberedCategoryOver.Groupoids.toBasedNatTrans η.hom.hom)
  map_id := sorry
  map_comp := sorry

/-- Package a cartesian functor between selected inverse-image targets as a morphism
of the packaged inverse-image algebraic stacks, after the universe bridge. -/
def inverseImage.ofCartesianFunctor (X Y : AlgebraicStacksOnSlice ι J S) :
    CartesianBasedFunctor (inverseImage.canonical ι J S X).target.p
        (inverseImage.canonical ι J S Y).target.p ⥤
      (inverseImage ι J S X ⟶ inverseImage ι J S Y) where
  obj F :=
    Bicategory.InducedBicategory.mkHom
      (FiberedCategoryOver.Groupoids.ofBasedFunctor
        (BasedFunctor.ofFunctor
          ((inverseImage.universeBridgeInv ι J S X).toFunctor ⋙
            F.toFunctor ⋙
            (inverseImage.universeBridge ι J S Y).toFunctor)
          sorry))
  map η :=
    Bicategory.InducedBicategory.mkHom₂
      (FiberedCategoryOver.Groupoids.ofBasedNatTrans
        { toNatTrans :=
            Functor.whiskerLeft (inverseImage.universeBridgeInv ι J S X).toFunctor
              (Functor.whiskerRight
                (CartesianBasedFunctor.toBasedNatTrans η).toNatTrans
                (inverseImage.universeBridge ι J S Y).toFunctor)
          isHomLift' := sorry })
  map_id := sorry
  map_comp := sorry

/-- Inverse image acts on morphism categories by the canonical pointwise Hom-functor
of `StackOver.InverseImage`, transported to morphisms of the packaged inverse-image
algebraic stacks. -/
def inverseImage.mapFunctor (X Y : AlgebraicStacksOnSlice ι J S) :
    (X ⟶ Y) ⥤ (inverseImage ι J S X ⟶ inverseImage ι J S Y) :=
  inverseImage.toCartesianFunctor ι J S X Y ⋙
    StackOver.InverseImage.Cartesian.pointwiseMapHom
      (inverseImage.canonical ι J S X) (inverseImage.canonical ι J S Y) ⋙
    inverseImage.ofCartesianFunctor ι J S X Y

/-- Inverse image induces equivalences of morphism categories of algebraic stacks. -/
instance inverseImage.mapFunctor.isEquivalence (X Y : AlgebraicStacksOnSlice ι J S) :
    (inverseImage.mapFunctor ι J S X Y).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicStacksOnSlice

namespace AlgebraicGeometry.AlgebraicStacks

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [(slicePost ι S).IsCocontinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]
variable [HasPullbacks (Over S)] [HasEqualizers (Over S)]
variable [PreservesLimitsOfShape WalkingCospan (slicePost ι S)]
variable [PreservesLimitsOfShape WalkingParallelPair (slicePost ι S)]
variable [Small.{w} (Over (ι.obj S))]

/-- A large-site algebraic stack over `ι.obj S` admits a presentation by inverse
images of algebraic spaces on the contained site. -/
def HasSmallSitePresentation (X' : AlgebraicStacks (ι.obj S)) : Prop :=
  ∃ (G : GroupoidOnSlice ι J S),
    GroupoidAlgebraicSpace.Smooth G.inverseImage ∧
      Nonempty (G.inverseImage.quotientStack ≌ toGroupoids X')

/-- The essential-image predicate unpacks as a smooth presentation `[U' / R']` of
`X'` whose object and arrow spaces are isomorphic to `f⁻¹U` and `f⁻¹R` for some
`U, R` in `Spaces / S`. -/
theorem HasSmallSitePresentation.spec (X' : AlgebraicStacks (ι.obj S))
    (h : HasSmallSitePresentation ι J S X') :
    ∃ (G : GroupoidOnSlice ι J S)
      (G' : GroupoidAlgebraicSpace (G.B.toAlgebraicSpace)),
      GroupoidAlgebraicSpace.Smooth G' ∧
        Nonempty (G'.quotientStack ≌ toGroupoids X') ∧
        Nonempty (G'.U.left ≅ G.U.toAlgebraicSpace) ∧
        Nonempty (G'.R.left ≅ G.R.toAlgebraicSpace) :=
  sorry

/-- A large-site algebraic stack is equivalent to the inverse image of a
contained-site algebraic stack if and only if it admits a presentation
`[U' / R']` with `U', R'` isomorphic to `f⁻¹U, f⁻¹R` for `U, R` in `Spaces / S`. -/
theorem essentiallyInImage_iff (X' : AlgebraicStacks (ι.obj S)) :
    (∃ (X : AlgebraicStacksOnSlice ι J S),
        Nonempty
          (toGroupoids (AlgebraicStacksOnSlice.inverseImage ι J S X) ≌
            toGroupoids X')) ↔
      HasSmallSitePresentation ι J S X' :=
  sorry

end AlgebraicGeometry.AlgebraicStacks
