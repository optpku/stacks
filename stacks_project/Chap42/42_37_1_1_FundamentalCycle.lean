module

public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import stacks_project.Chap42.Definition_42_19_1_Chow

@[expose] public section

universe u

/- The shared fundamental cycle is supported in its specified dimension. -/
#check (AlgebraicGeometry.AlgebraicCycle.fundamental_mem_dimensionSubgroup :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (d : X → ℤ) (k : ℤ),
    AlgebraicGeometry.AlgebraicCycle.fundamental d k ∈
      AlgebraicGeometry.AlgebraicCycle.dimensionSubgroup d k)

/- The shared fixed-dimension fundamental cycle has its expected type. -/
#check (AlgebraicGeometry.CycleGroup.fundamental :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (d : X → ℤ) (k : ℤ),
    AlgebraicGeometry.CycleGroup X d k)

/- Forgetting the degree recovers the underlying fundamental algebraic cycle. -/
#check (AlgebraicGeometry.CycleGroup.toAlgebraicCycle_fundamental :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (d : X → ℤ) (k : ℤ),
    AlgebraicGeometry.CycleGroup.toAlgebraicCycle d k
        (AlgebraicGeometry.CycleGroup.fundamental d k) =
      AlgebraicGeometry.AlgebraicCycle.fundamental d k)
