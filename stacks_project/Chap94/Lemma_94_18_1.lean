/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap78.Lemma_78_28_1
public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford
public import stacks_project.Chap94.Definition_94_16_4_Smooth
public import stacks_project.Chap94.Definition_94_16_5_Quotient

/-!
# Lemma 94.18.1

Change of big site preserves representability by a scheme, representability by
an algebraic space, being an algebraic stack, and being a Deligne-Mumford stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits
open scoped Bicategory

noncomputable section

universe u uC w

namespace AlgebraicGeometry.AlgebraicStack

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

/-- Lemma 94.18.1 (1): if a stack in groupoids `X` over `(Sch/S)_fppf` is
representable by a scheme `U : Over S`, then the inverse image of `X` along
the morphism of sites associated to `slicePost ι S` is representable by the
same scheme, now viewed as `(slicePost ι S).obj U` in `(Sch'/S)_fppf`. -/
@[stacks 04X2]
theorem inverseImage_representable_scheme (U : Over S) :
    Nonempty
      ((GroupoidOnSlice.discrete ι J S (OnSlice.ofYoneda ι J S U)).inverseImage.quotientStack ≌
        GroupoidsOver.slice ((slicePost ι S).obj U)) :=
  sorry

/-- The inverse image of a discrete scheme presentation is representable as a
category fibred in groupoids over the larger slice. -/
theorem inverseImage_isRepresentable_scheme (U : Over S) :
    FiberedCategoryOver.Groupoids.IsRepresentable
      (GroupoidOnSlice.discrete ι J S (OnSlice.ofYoneda ι J S U)).inverseImage.quotientStack :=
  sorry

/-- Lemma 94.18.1 (2): if a stack in groupoids `X` over `(Sch/S)_fppf` is
representable by an algebraic-space sheaf `F` on `J.over S`, then the inverse
image of `X` along `slicePost ι S` is representable by the algebraic space
`f⁻¹F`, constructed as `F.toAlgebraicSpace`. -/
@[stacks 04X2]
theorem inverseImage_representable_algebraicSpace (F : OnSlice ι J S) :
    IsRepresentableByAlgebraicSpace
      (GroupoidOnSlice.discrete ι J S F).inverseImage.quotientStack :=
  sorry

/-- The representing algebraic space in `inverseImage_representable_algebraicSpace`
is the inverse image `F.toAlgebraicSpace`. -/
theorem inverseImage_representable_algebraicSpace_spec (F : OnSlice ι J S) :
    Nonempty
      ((GroupoidOnSlice.discrete ι J S F).inverseImage.quotientStack ≌
        F.toAlgebraicSpace.toGroupoids) :=
  sorry

/-- Lemma 94.18.1 (3): if a stack in groupoids `X` over `(Sch/S)_fppf` is an
algebraic stack, then its inverse image along `slicePost ι S` is an algebraic
stack over `(Sch'/S)_fppf`. Unpacking via a smooth groupoid presentation `G`,
the large-site quotient `G.inverseImage.quotientStack` is algebraic. -/
@[stacks 04X2, instance]
instance inverseImage_algebraicStack (G : GroupoidOnSlice ι J S)
    [GroupoidAlgebraicSpace.Smooth G.inverseImage] :
    AlgebraicStack G.inverseImage.quotientStack :=
  sorry

/-- Lemma 94.18.1 (4): if a stack in groupoids `X` over `(Sch/S)_fppf` is a
Deligne-Mumford stack, then its inverse image along `slicePost ι S` is a
Deligne-Mumford stack over `(Sch'/S)_fppf`. Unpacking via an étale groupoid
presentation `G`, the large-site quotient `G.inverseImage.quotientStack` is
Deligne-Mumford. -/
@[stacks 04X2, instance]
instance inverseImage_deligneMumford (G : GroupoidOnSlice ι J S)
    [GroupoidAlgebraicSpace.Smooth G.inverseImage]
    [AlgebraicSpace.Etale G.inverseImage.s.left]
    [AlgebraicSpace.Etale G.inverseImage.t.left] :
    DeligneMumfordStack G.inverseImage.quotientStack :=
  sorry

end AlgebraicGeometry.AlgebraicStack
