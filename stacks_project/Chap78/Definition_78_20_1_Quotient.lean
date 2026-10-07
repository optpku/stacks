module

public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap78.«78_20_0_1_Points»

/-!
# Quotient stacks of groupoids in algebraic spaces

This module constructs the prestack `[U/_p R]` associated to a groupoid in algebraic spaces,
its selected fppf stackification `[U/R]`, and the canonical stackification comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open Functor.IsFibered.InGroupoids.Stackification
open Pseudofunctor.CoGrothendieck
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The prestack `[U/_p R]` associated to a groupoid in algebraic spaces, as the co-Grothendieck
projection of the groupoid-valued functor of points. -/
def preQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (groupoidPresheafProjection G.points)

/-- The projection of `[U/_p R]` is the co-Grothendieck projection of `G.points`. -/
theorem preQuotient_p {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (preQuotient G).p = groupoidPresheafProjection G.points := sorry

/-- The selected stackification presentation of `[U/_p R]` on `(Sch/S)_fppf`. -/
def stackificationPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    Presentation (Scheme.fppfTopology.over S) (preQuotient G).p :=
  presentation (Scheme.fppfTopology.over S) (preQuotient G).p

/-- The comparison of `stackificationPresentation G` is a stackification of `[U/_p R]`. -/
theorem stackificationPresentation_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S)
      (stackificationPresentation G).comparison := sorry

/-- The quotient stack `[U/R]` associated to a groupoid in algebraic spaces, obtained by
stackifying `[U/_p R]` on `(Sch/S)_fppf`. -/
def quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  (stackificationPresentation G).target

/-- The quotient stack is the target of the selected stackification of `[U/_p R]`. -/
theorem quotientStack_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    quotientStack G = (stackificationPresentation G).target := sorry

/-- The quotient stack `[U/R]` is a stack in groupoids on the big fppf site of `S`. -/
instance instIsStackInGroupoids_quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (quotientStack G).p :=
  StackOver.Groupoids.isStack (quotientStack G)

/-- The stackification comparison `1`-morphism `[U/_p R] ⟶ [U/R]`. -/
def stackificationHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    preQuotient G ⟶ (quotientStack G).toGroupoids :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (stackificationPresentation G).comparison.toBasedFunctor

/-- `stackificationHom` is a stackification of `[U/_p R]`. -/
theorem stackificationHom_isStackification {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.Hom.IsStackification
      (Scheme.fppfTopology.over S) (stackificationHom G) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
