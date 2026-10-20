module

public import ReasLib.AlgebraicGeometry.GroupScheme.ClassifyingStack
public import ReasLib.AlgebraicGeometry.Scheme.PowerSeries
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Classifying stacks of constant abelian schemes
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- The classifying stack of fppf torsors under the constant abelian scheme
associated to an abelian variety is algebraic. -/
instance instAlgebraicStack_classifyingTorsors {k : Type u} [Field k]
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] :
    AlgebraicStack (classifyingTorsors (constantAbelianScheme A0)) :=
  sorry

/-- The classifying stack of fppf torsors under a constant abelian scheme is
separated: its absolute groupoid diagonal is proper. -/
@[stacks 0AFD]
theorem classifyingTorsors_separated {k : Type u} [Field k]
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper (specPowerSeries k))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        (classifyingTorsors (constantAbelianScheme A0))) :=
  sorry

end AlgebraicGeometry.HomStack
