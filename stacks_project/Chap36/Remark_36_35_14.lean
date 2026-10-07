module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Lieblich
import StacksCheckRecall

universe u

/- Remark 36.35.14 (1): for a flat, locally finitely presented morphism, the original
relative-perfectness condition agrees with the bounded local model condition. -/
@[stacks 0DI9] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfectRelativeTo_iff_lieblichPerfectOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace),
      AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f E ↔
        AlgebraicGeometry.Scheme.ModuleDerived.IsLieblichPerfectOver f E)

/- Remark 36.35.14 (2): condition (B) is relative pseudo-coherence together with local finite
Tor dimension over the inverse-image structure sheaf of the base. -/
@[stacks 0DI9] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfectOver_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace),
      AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectOver f E ↔
        AlgebraicGeometry.Scheme.ModuleDerived.IsPseudoCoherentOver f E ∧
          AlgebraicGeometry.RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
            ((AlgebraicGeometry.RingedSpace.ModuleDerived.relativeRestriction
              f.toShHom).obj E))

/- Remark 36.35.14 (3): condition (B) defines a triangulated subcategory. -/
@[stacks 0DI9] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.perfectOver_isTriangulated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f],
      (AlgebraicGeometry.Scheme.ModuleDerived.perfectOver f).IsTriangulated)
