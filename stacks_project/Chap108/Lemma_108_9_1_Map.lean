module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Fibered.BasedCategory.CategoryOfElements
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.CategoryOfElements.Forward
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap108.Lemma_108_8_4_Stack

/-!
# The classifying morphism from the Picard stack to the Picard functor

The Picard functor on `(Sch/S)_fppf` is the fppf sheafification of fibrewise
isomorphism classes of `Picard.p f`. Its discrete stack in groupoids is the
target of the tautological iso-class morphism from `picardStack f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard functor of `f : X ⟶ B` as an fppf sheaf on `(Sch/S)`: the
sheafification of fibrewise isomorphism classes of invertible modules on the
fibres of `f`. -/
def functorOver (f : X ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (Functor.fiberIsoClassPresheaf (Picard.p f))

/-- The underlying presheaf of `functorOver f` is the fppf sheafification of
`Functor.fiberIsoClassPresheaf (Picard.p f)`. -/
theorem functorOver_val (f : X ⟶ B) :
    (functorOver f).obj =
      (Scheme.fppfTopology.over S).sheafify
        (Functor.fiberIsoClassPresheaf (Picard.p f)) :=
  sorry

/-- `functorOver f` is an fppf sheaf on `(Sch/S)`. -/
theorem functorOver_isSheaf (f : X ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (functorOver f).obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The discrete stack in groupoids associated to the Picard functor of `f` on
`(Sch/S)_fppf`. -/
def picardFunctorStack (f : X ⟶ B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  ((StackOver.Sets.ofSheaf (Scheme.fppfTopology.over S)).obj
      (RelativePicard.functorOver f)).toGroupoids

/-- The projection of `picardFunctorStack f` is the opposite category-of-elements
projection of `functorOver f`. -/
theorem picardFunctorStack_p (f : X ⟶ B) :
    (picardFunctorStack f).p =
      (CategoryOfElements.π (RelativePicard.functorOver f).obj).leftOp :=
  sorry

/-- The tautological classifying functor from Picard objects to sheafified
fibrewise isomorphism classes. -/
def toPicardFunctorFunctor (f : X ⟶ B) :
    (picardStack f).total ⥤ (picardFunctorStack f).total :=
  CategoryOfElements.Section.functor (Picard.p f)
      (Functor.fiberIsoClassPresheaf (Picard.p f))
      (Functor.fiberIsoClassPresheaf.tautologicalSection (Picard.p f)) ⋙
    (CategoryOfElements.map
      ((sheafificationAdjunction (Scheme.fppfTopology.over S) (Type (u + 1))).unit.app
        (Functor.fiberIsoClassPresheaf (Picard.p f)))).op

/-- The tautological classifying functor lies strictly over `(Sch/S)`. -/
theorem toPicardFunctorFunctor_comp_p (f : X ⟶ B) :
    toPicardFunctorFunctor f ⋙ (picardFunctorStack f).p = (picardStack f).p :=
  sorry

/-- The tautological classifying functor as a based functor over `(Sch/S)`.
The Picard stack has Hom-universe `u + 1` while the discrete iso-class stack
has Hom-universe `u`, so this is a heterogeneous based functor rather than a
`StackOver.Groupoids` 1-morphism. -/
def toPicardFunctorBasedFunctor (f : X ⟶ B) :
    BasedCategory.ofFunctor (picardStack f).p ⥤ᵇ
      BasedCategory.ofFunctor (picardFunctorStack f).p :=
  BasedFunctor.ofFunctor (toPicardFunctorFunctor f) (toPicardFunctorFunctor_comp_p f)

/-- The canonical classifying morphism from the Picard stack of `f` to the
discrete stack of the Picard functor, sending an invertible module on a fibre
to its sheafified isomorphism class. -/
def toPicardFunctor (f : X ⟶ B) :
    CartesianBasedFunctor (picardStack f).p (picardFunctorStack f).p :=
  CartesianBasedFunctor.ofTargetInGroupoids (toPicardFunctorBasedFunctor f)

/-- The based functor underlying `toPicardFunctor f` is
`toPicardFunctorBasedFunctor f`. -/
theorem toPicardFunctor_toBasedFunctor (f : X ⟶ B) :
    (toPicardFunctor f).toBasedFunctor = toPicardFunctorBasedFunctor f :=
  sorry

/-- On a Picard object `x`, `toPicardFunctor f` is the sheafification unit of the
displayed fibrewise isomorphism class of `x`. -/
theorem toPicardFunctor_app_mk (f : X ⟶ B) (x : Picard.Obj f) :
    (toPicardFunctor f).toBasedFunctor.toFunctor.obj x =
      op
        ((RelativePicard.functorOver f).obj.elementsMk (op ((Picard.p f).obj x))
          (((sheafificationAdjunction (Scheme.fppfTopology.over S)
                (Type (u + 1))).unit.app
              (Functor.fiberIsoClassPresheaf (Picard.p f))).app
            (op ((Picard.p f).obj x)) (Quotient.mk'' ⟨x, rfl⟩))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
