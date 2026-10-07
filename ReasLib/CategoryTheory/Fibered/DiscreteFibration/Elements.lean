module

-- The instance type exposes both the discrete-fibration predicate and mathlib's canonical
-- category-of-elements projection, so both imports are public.
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Basic
public import Mathlib.CategoryTheory.Elements
import Mathlib.Tactic.CrossRefAttribute

/-!
# Categories of elements as discrete fibrations

The opposite category-of-elements projection of a set-valued presheaf has unique lifts and hence
is a discrete fibration.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

open Opposite

/-- The domain of the canonical lift of `f` through the opposite category-of-elements
projection. Its element is obtained by applying the presheaf to `f.op`. -/
@[stacks 04TM "canonical category-of-elements lift domain"]
def liftDomain
    (F : Cᵒᵖ ⥤ Type w) {R : C} {a : F.Elementsᵒᵖ}
    (f : R ⟶ ((π F).leftOp).obj a) :
    F.Elementsᵒᵖ :=
  op ⟨op R, F.map f.op (unop a).2⟩

/-- The underlying arrow in `Cᵒᵖ` of the canonical category-of-elements lift. -/
def liftHomVal
    (F : Cᵒᵖ ⥤ Type w) {R : C} {a : F.Elementsᵒᵖ}
    (f : R ⟶ ((π F).leftOp).obj a) :
    (unop a).1 ⟶ (unop (liftDomain F f)).1 :=
  f.op

/-- The underlying arrow of the canonical lift carries the element of its source to the
reindexed element in its target. -/
@[simp]
theorem liftHomVal.map
    (F : Cᵒᵖ ⥤ Type w) {R : C} {a : F.Elementsᵒᵖ}
    (f : R ⟶ ((π F).leftOp).obj a) :
    F.map (liftHomVal F f) (unop a).2 = (unop (liftDomain F f)).2 := sorry

/-- The canonical morphism in the opposite category of elements lifting `f`. -/
@[stacks 04TM "canonical category-of-elements lift morphism"]
def liftHom
    (F : Cᵒᵖ ⥤ Type w) {R : C} {a : F.Elementsᵒᵖ}
    (f : R ⟶ ((π F).leftOp).obj a) :
    liftDomain F f ⟶ a :=
  (homMk (unop a) (unop (liftDomain F f))
    (liftHomVal F f) (liftHomVal.map F f)).op

/- Axiom audit: `liftDomain` and `liftHomVal` contain the complete non-`Prop` payload of the
canonical lift and do not use choice or `sorryAx`. The `sorryAx` visible on `liftHom` is confined
to the equality proof stored by a category-of-elements morphism. -/

/-- The canonical category-of-elements morphism lies over the prescribed base arrow. -/
theorem liftHom.isHomLift
    (F : Cᵒᵖ ⥤ Type w) {R : C} {a : F.Elementsᵒᵖ}
    (f : R ⟶ ((π F).leftOp).obj a) :
    ((π F).leftOp).IsHomLift f (liftHom F f) := sorry

/-- The complete canonical lift package for the opposite category-of-elements projection. -/
@[stacks 04TM "canonical category-of-elements lift"]
def homLift
    (F : Cᵒᵖ ⥤ Type w) {R : C} {a : F.Elementsᵒᵖ}
    (f : R ⟶ ((π F).leftOp).obj a) :
    Functor.HomLift ((π F).leftOp) f where
  domain := liftDomain F f
  hom := liftHom F f
  isHomLift := liftHom.isHomLift F f

/-- Any two lifts through the opposite category-of-elements projection with the same displayed
base arrow and codomain coincide. -/
theorem homLift.unique
    (F : Cᵒᵖ ⥤ Type w) {R : C} {a : F.Elementsᵒᵖ}
    (f : R ⟶ ((π F).leftOp).obj a)
    (l₁ l₂ : Functor.HomLift ((π F).leftOp) f) :
    l₁ = l₂ := sorry

/-- Example 4.38.5 (Stacks 04TM): the contravariant category-of-elements projection of a
set-valued presheaf is a discrete fibration. -/
@[stacks 04TM "the projection is a discrete fibration"]
instance π.leftOp.isDiscreteFibration
    (F : Cᵒᵖ ⥤ Type w) :
    Functor.IsDiscreteFibration ((π F).leftOp) where
  homLiftNonempty f := ⟨homLift F f⟩
  homLiftSubsingleton f := ⟨homLift.unique F f⟩
/- Proof strategy: for `f : V ⟶ U` and `x : F.obj (op U)`, take the lift whose domain is
`op ⟨op V, F.map f.op x⟩` and whose arrow is the opposite of
`homMk _ _ f.op rfl`. This lift is unique: any competing lift has the same base arrow by its
`IsHomLift` field, its domain element is then forced by the category-of-elements equation, and
`Functor.Elements.ext` together with `CategoryOfElements.ext` identifies the complete
`Functor.HomLift` package. This proves the primitive unique-lifting owner directly, without
detouring through fibredness plus a separate discreteness-of-fibres theorem. -/

end CategoryOfElements

end CategoryTheory
