module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper
public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Projection

/-!
# The stack of finite-type algebraic spaces

The full subcategory of `Spaces` on pairs `X / U` whose structure morphism is of
finite type, its restricted projection, and its stack structure over the fppf site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

namespace FiniteType

/-- Package a finite-type morphism `X ⟶ ofOver U` as an object of the full
subcategory. -/
def mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] :
    (Spaces.finiteType S).FullSubcategory where
  obj := Spaces.mk pX
  property := (inferInstance : FiniteType pX)

/-- The underlying object of `mk pX` is `Spaces.mk pX`. -/
theorem mk_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] :
    (mk pX).obj = Spaces.mk pX :=
  sorry

/-- Objects of the finite-type full subcategory have finite-type structure
morphisms. -/
instance instFiniteType {S : Scheme.{u}}
    (x : (Spaces.finiteType S).FullSubcategory) :
    FiniteType x.obj.hom :=
  x.property

/-- The inclusion of finite-type objects into `Spaces`. -/
abbrev inclusion (S : Scheme.{u}) :
    (Spaces.finiteType S).FullSubcategory ⥤ Spaces S :=
  (Spaces.finiteType S).ι

/-- The projection from finite-type algebraic spaces is the restriction of
`Spaces.p` to the finite-type full subcategory. -/
def p (S : Scheme.{u}) : (Spaces.finiteType S).FullSubcategory ⥤ Over S :=
  (Spaces.finiteType S).ι ⋙ (Spaces.p : Spaces S ⥤ Over S)

/-- The restricted projection is the inclusion followed by `Spaces.p`. -/
theorem inclusion_comp_p (S : Scheme.{u}) :
    inclusion S ⋙ (Spaces.p : Spaces S ⥤ Over S) = p S :=
  sorry

/-- The restricted projection sends `mk pX` to the scheme `U` over `S`. -/
theorem p_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] : (p S).obj (mk pX) = U :=
  sorry

/-- The restricted projection sends a morphism to its underlying morphism of
schemes over `S`. -/
theorem p_map {S : Scheme.{u}} {x y : (Spaces.finiteType S).FullSubcategory}
    (φ : x ⟶ y) : (p S).map φ = φ.hom.right :=
  sorry

/-- Finite type of structure morphisms is stable under strongly cartesian
pullback in `Spaces`. -/
theorem cartesianPullback (S : Scheme.{u}) :
    ObjectProperty.IsStableUnder.CartesianPullback (Spaces.finiteType S)
      (Spaces.p : Spaces S ⥤ Over S) :=
  sorry

/-- The projection from finite-type algebraic spaces is a stack over the fppf
site of schemes over the base. -/
instance instIsStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p S) :=
  sorry

/-- The stack of finite-type algebraic spaces over the fppf site of schemes
over `S`. -/
abbrev stack (S : Scheme.{u}) : StackOver (Scheme.fppfTopology.over S) :=
  StackOver.ofProjection (Scheme.fppfTopology.over S) (p S)

/-- The projection of `stack S` is the functor `p S`. -/
theorem stack_p (S : Scheme.{u}) : (stack S).p = p S :=
  sorry

end FiniteType

end AlgebraicGeometry.AlgebraicSpace.Spaces
