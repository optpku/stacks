module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CardinalType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Projection
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Stacks of algebraic spaces with cardinal size bounds

The countable locally finite type and cardinal type conditions cut out full
subcategories of algebraic spaces over schemes. Their projections define fppf
stacks admitting full subcategories with small fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CountablyAffineLocallyOfFiniteType

/-- Objects `X / U` of `Spaces S` that are locally of finite type with
countable affine inverse images of affine opens. -/
def objectProperty (S : Scheme.{u}) : ObjectProperty (Spaces S) :=
  fun P ↦ CountablyAffineLocallyOfFiniteType P.hom

/-- Membership in the countable locally finite type cut is the morphism
property on `P.hom`. -/
theorem objectProperty_iff (S : Scheme.{u}) (P : Spaces S) :
    objectProperty S P ↔ CountablyAffineLocallyOfFiniteType P.hom :=
  Iff.rfl

/-- The forgetful functor from countable locally finite type algebraic spaces
over schemes over `S`. -/
def forget (S : Scheme.{u}) : (objectProperty S).FullSubcategory ⥤ Over S :=
  (objectProperty S).ι ⋙ (Spaces.p : Spaces S ⥤ Over S)

/-- The forgetful functor is a stack over `(Sch/S)_fppf`. -/
instance forget_isStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (forget S) :=
  sorry

/-- The stack of countable locally finite type algebraic spaces over
`(Sch/S)_fppf`. -/
def stack (S : Scheme.{u}) : StackOver (Scheme.fppfTopology.over S) :=
  StackOver.ofProjection (Scheme.fppfTopology.over S) (forget S)

/-- The projection of the countable locally finite type stack is `forget`. -/
theorem stack_p (S : Scheme.{u}) : (stack S).p = forget S := rfl

/-- The stack admits an essentially surjective full subcategory whose
restricted projection is an fppf stack with small fibers. -/
theorem exists_smallSubcategory (S : Scheme.{u}) :
    ∃ P : ObjectProperty (stack S).total,
      P.ι.EssSurj ∧
        IsStack.OnSite (Scheme.fppfTopology.over S) (P.ι ⋙ (stack S).p) ∧
        ∀ U : Over S, Small.{u} ((P.ι ⋙ (stack S).p).Fiber U) :=
  sorry

end CountablyAffineLocallyOfFiniteType

namespace OfCardinalType

/-- Objects `X / U` of `Spaces S` whose structure morphism is of `κ`-type. -/
def objectProperty (κ : Cardinal.{u}) (S : Scheme.{u}) :
    ObjectProperty (Spaces S) :=
  fun P ↦ OfCardinalType κ P.hom

/-- Membership in the `κ`-type cut is the morphism property on `P.hom`. -/
theorem objectProperty_iff (κ : Cardinal.{u}) (S : Scheme.{u})
    (P : Spaces S) :
    objectProperty κ S P ↔ OfCardinalType κ P.hom :=
  Iff.rfl

/-- The forgetful functor from algebraic spaces of `κ`-type over schemes
over `S`. -/
def forget (κ : Cardinal.{u}) (S : Scheme.{u}) :
    (objectProperty κ S).FullSubcategory ⥤ Over S :=
  (objectProperty κ S).ι ⋙ (Spaces.p : Spaces S ⥤ Over S)

/-- The forgetful functor of `κ`-type spaces is a stack over `(Sch/S)_fppf`. -/
instance forget_isStackOnSite (κ : Cardinal.{u}) (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (forget κ S) :=
  sorry

/-- The stack `Spaces_κ` of morphisms of `κ`-type over `(Sch/S)_fppf`. -/
def stack (κ : Cardinal.{u}) (S : Scheme.{u}) :
    StackOver (Scheme.fppfTopology.over S) :=
  StackOver.ofProjection (Scheme.fppfTopology.over S) (forget κ S)

/-- The projection of `Spaces_κ` is the `κ`-type forgetful functor. -/
theorem stack_p (κ : Cardinal.{u}) (S : Scheme.{u}) :
    (stack κ S).p = forget κ S :=
  rfl

/-- The stack admits an essentially surjective full subcategory whose
restricted projection is an fppf stack with small fibers. -/
theorem exists_smallSubcategory (κ : Cardinal.{u}) (S : Scheme.{u}) :
    ∃ P : ObjectProperty (stack κ S).total,
      P.ι.EssSurj ∧
        IsStack.OnSite (Scheme.fppfTopology.over S) (P.ι ⋙ (stack κ S).p) ∧
        ∀ U : Over S, Small.{u} ((P.ι ⋙ (stack κ S).p).Fiber U) :=
  sorry

end OfCardinalType

end AlgebraicGeometry.AlgebraicSpace
