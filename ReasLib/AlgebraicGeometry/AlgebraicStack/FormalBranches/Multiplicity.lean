/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches.Components
public import ReasLib.AlgebraicGeometry.AlgebraicStack.IrreducibleComponent.Multiplicity
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FormalBranches

/-- Pointed-identified components of formal objects have equal multiplicities. -/
theorem componentMultiplicity_eq_of_pointedIdentified
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (ξ η : GroupoidsOver.FormalObject X)
    (mξ : StageOneMarking x0 ξ) (mη : StageOneMarking x0 η)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier))
    (W : irreducibleComponents (PrimeSpectrum η.base.carrier))
    (h : PointedIdentified x0 ξ η mξ mη Z W) :
    Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of ξ.base.carrier)) Z =
      Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of η.base.carrier)) W :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FormalBranches

namespace AlgebraicGeometry.AlgebraicStack

/-- The multiplicity of a formal branch is the multiplicity of the corresponding
irreducible component of the spectrum of any marked versal formal object. -/
@[stacks 0DRC]
def formalBranchMultiplicity
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom] :
    FormalBranches x0 → ℕ :=
  Quot.lift
    (fun r : FormalBranches.BranchRep x0 =>
      Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of r.1.base.carrier))
        r.2.2.2)
    (fun r r' h => FormalBranches.componentMultiplicity_eq_of_pointedIdentified
      x0 r.1 r'.1 r.2.2.1 r'.2.2.1 r.2.2.2 r'.2.2.2 h)

/-- The multiplicity of a branch represented by a marked versal component equals
the multiplicity of that component in the spectrum of the versal ring. -/
theorem formalBranchMultiplicity_eq
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (ξ : GroupoidsOver.FormalObject X) [GroupoidsOver.FormalObject.IsVersal ξ]
    (mξ : StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    formalBranchMultiplicity x0 (FormalBranches.mk x0 ξ mξ Z) =
      Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of ξ.base.carrier)) Z :=
  rfl

/-- The multiplicity of a branch represented by a marked versal component coerces
to the length of the spectrum stalk at the generic point of that component. -/
theorem coe_formalBranchMultiplicity
    {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (ξ : GroupoidsOver.FormalObject X) [GroupoidsOver.FormalObject.IsVersal ξ]
    (mξ : StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    (formalBranchMultiplicity x0 (FormalBranches.mk x0 ξ mξ Z) : ℕ∞) =
      Module.length
        ((Spec (CommRingCat.of ξ.base.carrier)).presheaf.stalk Z.2.1.genericPoint)
        ((Spec (CommRingCat.of ξ.base.carrier)).presheaf.stalk Z.2.1.genericPoint) := by
  rw [formalBranchMultiplicity_eq]
  exact Scheme.coe_irreducibleComponentMultiplicity (Spec (CommRingCat.of ξ.base.carrier)) Z

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.FormalBranches

/-- For an algebraic stack locally of finite type over a locally Noetherian
scheme, the component map from formal branches through a finite type
field-valued point preserves multiplicities if the stalk of the base at the
image point is a G-ring. The multiplicity of each marked versal component
equals the multiplicity of its image component of the stack. -/
@[stacks 0DRD]
theorem toComponent_multiplicity {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    [IsLocallyNoetherian X] (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (s : S) (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (hξ : StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of ξ.base.carrier)) Z =
      irreducibleComponentMultiplicity X τ (toComponent x0 hτ (mk x0 ξ hξ Z)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FormalBranches
