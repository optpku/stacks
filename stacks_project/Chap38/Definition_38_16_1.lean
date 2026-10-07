module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Definition 38.16.1 (1): a finite type quasicoherent module is pure along a fibre
when no elementary impurity lies above the corresponding base point. -/
@[stacks 05J4] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S), Prop)

/- Definition 38.16.1 (2): universal purity along a fibre excludes every impurity
above the corresponding base point. -/
@[stacks 05J4] #check
  (AlgebraicGeometry.Scheme.Modules.IsUniversallyPureAlong :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S), Prop)

/- Definition 38.16.1 (3): a scheme is pure along a fibre when its structure sheaf is. -/
@[stacks 05J4] #check
  (AlgebraicGeometry.Scheme.IsPureAlong :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] (s : S), Prop)

/- Definition 38.16.1 (4): universal relative purity means universal purity along
every fibre. -/
@[stacks 05J4] #check
  (AlgebraicGeometry.Scheme.Modules.IsUniversallyPureOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

/- Definition 38.16.1 (5): relative purity means purity along every fibre. -/
@[stacks 05J4] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

/- Definition 38.16.1 (6): a scheme is pure relative to the base when its structure
sheaf is pure relative to the base. -/
@[stacks 05J4] #check
  (AlgebraicGeometry.Scheme.IsPureOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f], Prop)
