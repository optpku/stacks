module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Base change of algebraic spaces of finite presentation

Restriction of functors of points along a morphism of base schemes preserves
finite presentation and commutes with composition of base morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite presentation over the base is stable under base change of the base
scheme. -/
instance baseChange_finitePresentation {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : AlgebraicSpace S') [FinitePresentation (SchemeRealization.toBase X)] :
    FinitePresentation (SchemeRealization.toBase (baseChange g X)) :=
  sorry

namespace FinitePresentationOver

/-- Base change along `g : S ⟶ S'` sends algebraic spaces of finite presentation
over `S'` to algebraic spaces of finite presentation over `S`. -/
theorem mapsTo {S S' : Scheme.{u}} (g : S ⟶ S') :
    finitePresentationOverProperty S' ≤
      (finitePresentationOverProperty S).inverseImage (baseChangeFunctor g) :=
  sorry

/-- Base change as a functor on categories of algebraic spaces of finite
presentation. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') :
    FinitePresentationOver S' ⥤ FinitePresentationOver S :=
  FullSubcategory.restrict (baseChangeFunctor g) (mapsTo g)

/-- The underlying algebraic space of a restricted base change is the ambient
base change. -/
@[simp]
theorem baseChange_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : FinitePresentationOver S') :
    ((baseChange g).obj X).obj = AlgebraicSpace.baseChange g X.obj :=
  rfl

/-- Restricted base change is transitive in the base morphism. -/
def compIso {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
  NatIso.ofComponents
    (fun X ↦ (finitePresentationOverProperty S).isoMk
      ((baseChangeFunctor_comp f g).app X.obj))
    sorry

end FinitePresentationOver

end AlgebraicGeometry.AlgebraicSpace
