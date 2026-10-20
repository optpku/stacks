module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat

/-!
# Parasitic presheaves of modules on an algebraic stack

A presheaf of `𝒪_X`-modules on an algebraic stack is parasitic when it
vanishes on every object whose 2-Yoneda morphism from the underlying scheme
is a flat morphism of algebraic stacks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids Functor.Fiber Opposite Limits
open scoped Bicategory ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- A presheaf of `𝒪_X`-modules is parasitic if it vanishes on every object
`x` of `X` lying over a scheme `U` whose 2-Yoneda morphism `U ⟶ X` is a
flat morphism of algebraic stacks. -/
class IsParasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : PresheafOfModules.{u} (structureSheaf X).obj) : Prop where
  /-- The value `F(x)` is the zero module whenever `x : U ⟶ X` is flat. -/
  isZero_of_flat : ∀ {U : Over S} (x : X.p.Fiber U),
    AlgebraicStack.Flat (YonedaSlice.representative x) →
      IsZero (F.obj (op (fiberInclusion.obj x)))

/-- A presheaf `F` is parasitic if and only if `F(x) = 0`
whenever the 2-Yoneda morphism of `x` is a flat morphism of algebraic stacks. -/
theorem isParasitic_spec {X : GroupoidsOver S} [AlgebraicStack X]
    (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    IsParasitic F ↔
      ∀ {U : Over S} (x : X.p.Fiber U),
        AlgebraicStack.Flat (YonedaSlice.representative x) →
          IsZero (F.obj (op (fiberInclusion.obj x))) :=
  sorry

/-- A parasitic presheaf of `𝒪_X`-modules vanishes on a specified object whose
2-Yoneda morphism is flat. -/
theorem IsParasitic.isZero {X : GroupoidsOver S} [AlgebraicStack X]
    {F : PresheafOfModules.{u} (structureSheaf X).obj} [IsParasitic F]
    {U : Over S} (x : X.p.Fiber U)
    (hx : AlgebraicStack.Flat (YonedaSlice.representative x)) :
    IsZero (F.obj (op (fiberInclusion.obj x))) :=
  sorry

/-- The zero presheaf of `𝒪_X`-modules. -/
def zero (X : GroupoidsOver S) :
    PresheafOfModules.{u} (structureSheaf X).obj where
  obj _ := 0
  map _ := 0

/-- Evaluation of the zero presheaf of `𝒪_X`-modules is the zero module. -/
theorem zero_obj (X : GroupoidsOver S) (x : X.totalᵒᵖ) :
    (zero X).obj x = 0 :=
  sorry

/-- The zero presheaf of `𝒪_X`-modules is a zero object. -/
theorem isZero_zero (X : GroupoidsOver S) :
    IsZero (zero X) :=
  sorry

/-- A zero object in `PMod(𝒪_X)` is parasitic. -/
theorem isParasitic_of_isZero {X : GroupoidsOver S} [AlgebraicStack X]
    {F : PresheafOfModules.{u} (structureSheaf X).obj} (hF : IsZero F) :
    IsParasitic F :=
  sorry

/-- The zero presheaf of `𝒪_X`-modules is parasitic. -/
instance instIsParasitic_of_isZero {X : GroupoidsOver S} [AlgebraicStack X] :
    IsParasitic (zero X) :=
  sorry

/-- The parasitic property is invariant under isomorphism of presheaves of
`𝒪_X`-modules. -/
theorem isParasitic_iff_of_iso {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : PresheafOfModules.{u} (structureSheaf X).obj} (e : F ≅ G) :
    IsParasitic F ↔ IsParasitic G :=
  sorry

/-- The object property of parasitic presheaves of `𝒪_X`-modules. -/
abbrev parasitic (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (PresheafOfModules.{u} (structureSheaf X).obj) :=
  IsParasitic

/-- Membership in `parasitic X` is the class `IsParasitic`. -/
theorem mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    parasitic X F ↔ IsParasitic F :=
  sorry

end AlgebraicGeometry.GroupoidsOver

