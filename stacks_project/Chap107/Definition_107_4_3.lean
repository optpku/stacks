module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches.Multiplicity
import StacksCheckRecall

/-!
# Multiplicity of a formal branch

The multiplicity of a formal branch of an algebraic stack through a finite-type
field-valued point is the multiplicity of the corresponding irreducible component
of the spectrum of any versal ring at that point.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Definition 107.4.3: the multiplicity of a formal branch is computed from any
marked versal representative. -/
@[stacks 0DRC] #check (AlgebraicGeometry.AlgebraicStack.formalBranchMultiplicity :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicGeometry.AlgebraicStack.IsLocallyOfFiniteType X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom],
    AlgebraicGeometry.AlgebraicStack.FormalBranches x0 → ℕ)

#check (AlgebraicGeometry.AlgebraicStack.formalBranchMultiplicity_eq :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicGeometry.AlgebraicStack.IsLocallyOfFiniteType X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (ξ : GroupoidsOver.FormalObject X) [GroupoidsOver.FormalObject.IsVersal ξ]
    (mξ : AlgebraicGeometry.AlgebraicStack.StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)),
    AlgebraicGeometry.AlgebraicStack.formalBranchMultiplicity x0
      (AlgebraicGeometry.AlgebraicStack.FormalBranches.mk x0 ξ mξ Z) =
      Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of ξ.base.carrier)) Z)
