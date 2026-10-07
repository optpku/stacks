module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Transitivity.Derived
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated DerivedCategory

universe u

/- Lemma 37.13.11: for composable scheme morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`,
with `f` locally a complete intersection, the canonical naive-cotangent transitivity triangle
is distinguished in `D(𝒪_X)`. -/
@[stacks 0FV3] #check
  (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.triangle_distinguished :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfType RingHom.IsLocalCompleteIntersection f],
      AlgebraicGeometry.Scheme.Hom.NaiveCotangent.triangle f g ∈
        distTriang (RingedSpace.ModuleDerived X.toRingedSpace))

/- The canonical triangle underlying the distinguishedness statement. -/
#check (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.triangle :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f],
    Triangle (RingedSpace.ModuleDerived X.toRingedSpace))

/- Its six-term homology segment is canonically identified with the naive-cotangent
transitivity sequence. -/
#check (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.sixTermIso :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f],
    CategoryTheory.Functor.homologySequenceComposableArrows₅
        (DerivedCategory.homologyFunctor X.toRingedSpace.Modules 0)
        (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.triangle f g) (-1) 0 rfl ≅
      (RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom).sixTerm)
