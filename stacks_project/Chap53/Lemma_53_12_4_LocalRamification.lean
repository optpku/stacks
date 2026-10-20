module

public import ReasLib.AlgebraicGeometry.Curve.Ramification
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Curve
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

/- Lemma 53.12.4 local ramification definitions and computation bridges. -/
@[stacks 0C1F] #check
  (AlgebraicGeometry.Scheme.Hom.ramificationIndexAt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X), ℕ)

@[stacks 0C1F] #check
  (AlgebraicGeometry.Scheme.Hom.ramificationIndexAt_eq_ramificationIdx :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
      f.ramificationIndexAt x =
        @Ideal.ramificationIdx (X.presheaf.stalk x) _
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (Y.presheaf.stalk (f x)) _ (f.stalkAlgebra x))

@[stacks 0C1F] #check
  (AlgebraicGeometry.Curve.kaehlerDifferentMultiplicity :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} (f : X ⟶ Y)
      [LocallyOfFiniteType f.left] (x : closedPoints X.left), ℕ)

@[stacks 0C1F] #check
  (AlgebraicGeometry.Curve.kaehlerDifferentMultiplicity_def :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} (f : X ⟶ Y)
      [LocallyOfFiniteType f.left] (x : closedPoints X.left),
      kaehlerDifferentMultiplicity f x =
        (Module.length (stalkRing X x.1)
          (RingedSpace.stalkModuleCat
            (closedSubschemeStructureSheafOn (kaehlerDifferent f.left)) x.1)).toNat)
