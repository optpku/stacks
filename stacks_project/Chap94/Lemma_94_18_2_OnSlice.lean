/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Construction
public import stacks_project.Chap78.Lemma_78_28_1_Quotient
public import stacks_project.Chap94.Definition_94_16_4_Smooth

/-!
# Algebraic stacks on a contained big site

An algebraic stack over `S` defined using a fully faithful contained site `(C, J)`
is a stack in groupoids on `J.over S` that admits a smooth groupoid presentation
in algebraic spaces on that site. The associated 2-category is the full
sub-2-category of `StackOver.Groupoids (J.over S)` on this property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits
open scoped Bicategory

noncomputable section

universe u uC

namespace AlgebraicGeometry.AlgebraicStack

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]

/-- An algebraic stack over `S` defined using the contained site `(C, J)` is a stack
in groupoids on `J.over S` that admits a presentation `[U / R]` by a groupoid in
algebraic spaces on that site whose inverse image along `slicePost ι S` is smooth. -/
class OnSlice (X : StackOver.Groupoids (J.over S)) : Prop where
  /-- There is a contained-site groupoid `(U, R, s, t, c)` with `U, R` algebraic spaces
  on `J.over S`, such that `[U / R] ⟶ X` is an equivalence and the inverse-image
  groupoid is smooth. -/
  exists_presentation :
    ∃ (G : GroupoidOnSlice ι J S) (f : sliceQuotientStack ι J S G ⟶ X),
      GroupoidAlgebraicSpace.Smooth G.inverseImage ∧
        StackOver.Groupoids.Hom.IsEquivalence f

namespace OnSlice

/-- The object property on stacks in groupoids over `J.over S` selecting algebraic
stacks defined using the contained site. -/
def objectProperty : ObjectProperty (StackOver.Groupoids (J.over S)) :=
  fun X ↦ OnSlice ι J S X

/-- The object property of contained-site algebraic stacks is the class `OnSlice`. -/
theorem objectProperty_apply (X : StackOver.Groupoids (J.over S)) :
    objectProperty ι J S X ↔ OnSlice ι J S X := sorry

/-- A stack in groupoids over `J.over S` is a contained-site algebraic stack if and
only if it admits a smooth inverse-image groupoid presentation. -/
theorem iff (X : StackOver.Groupoids (J.over S)) :
    OnSlice ι J S X ↔
      ∃ (G : GroupoidOnSlice ι J S) (f : sliceQuotientStack ι J S G ⟶ X),
        GroupoidAlgebraicSpace.Smooth G.inverseImage ∧
          StackOver.Groupoids.Hom.IsEquivalence f := sorry

/-- A contained-site algebraic stack admits a smooth inverse-image groupoid
presentation `[U / R] ⟶ X`. -/
theorem spec (X : StackOver.Groupoids (J.over S)) [OnSlice ι J S X] :
    ∃ (G : GroupoidOnSlice ι J S) (f : sliceQuotientStack ι J S G ⟶ X),
      GroupoidAlgebraicSpace.Smooth G.inverseImage ∧
        StackOver.Groupoids.Hom.IsEquivalence f := sorry

/-- The quotient stack of a contained-site groupoid whose inverse image is smooth is
an algebraic stack on that site. -/
instance instOnSlice (G : GroupoidOnSlice ι J S)
    [GroupoidAlgebraicSpace.Smooth G.inverseImage] :
    OnSlice ι J S (GroupoidAlgebraicSpace.sliceQuotientStack ι J S G) := sorry

end OnSlice

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]

/-- The 2-category of algebraic stacks over `S` defined using the contained site
`(C, J)`, as the full sub-2-category of `StackOver.Groupoids (J.over S)` on
`AlgebraicStack.OnSlice`. -/
abbrev AlgebraicStacksOnSlice :=
  (AlgebraicStack.OnSlice.objectProperty ι J S).FullSubbicategory

namespace AlgebraicStacksOnSlice

/-- Package a stack in groupoids over `J.over S` that is algebraic on the contained
site as an object of `AlgebraicStacksOnSlice`. -/
def of (X : StackOver.Groupoids (J.over S)) [AlgebraicStack.OnSlice ι J S X] :
    AlgebraicStacksOnSlice ι J S :=
  ObjectProperty.FullSubbicategory.mk
    (AlgebraicStack.OnSlice.objectProperty ι J S) X ‹AlgebraicStack.OnSlice ι J S X›

/-- The underlying stack in groupoids over `J.over S`. -/
abbrev toGroupoids (X : AlgebraicStacksOnSlice ι J S) :
    StackOver.Groupoids (J.over S) :=
  X.1

/-- The underlying ordinary stack over `J.over S`. -/
abbrev toStackOver (X : AlgebraicStacksOnSlice ι J S) : StackOver (J.over S) :=
  StackOver.Groupoids.toStackOver (toGroupoids ι J S X)

/-- The canonical inclusion of contained-site algebraic stacks into stacks in
groupoids over `J.over S`. -/
abbrev forget :
    StrictPseudofunctor (AlgebraicStacksOnSlice ι J S)
      (StackOver.Groupoids (J.over S)) :=
  ObjectProperty.FullSubbicategory.ι (AlgebraicStack.OnSlice.objectProperty ι J S)

/-- The underlying stack in groupoids of an object of `AlgebraicStacksOnSlice` is
algebraic on the contained site. -/
instance mem (X : AlgebraicStacksOnSlice ι J S) :
    AlgebraicStack.OnSlice ι J S (toGroupoids ι J S X) :=
  X.property

/-- Packaging a stack in groupoids as a contained-site algebraic stack forgets to
the original object. -/
theorem of_toGroupoids (X : StackOver.Groupoids (J.over S))
    [AlgebraicStack.OnSlice ι J S X] :
    toGroupoids ι J S (of ι J S X) = X := sorry

/-- The inclusion into stacks in groupoids sends a contained-site algebraic stack
to its underlying object. -/
theorem forget_obj (X : AlgebraicStacksOnSlice ι J S) :
    (forget ι J S).obj X = toGroupoids ι J S X := sorry

end AlgebraicStacksOnSlice

end AlgebraicGeometry
