/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.Specialization.BaseChange
import StacksCheckRecall

/-!
# Lemma 62.4.3

Specialization of cycles over a discrete valuation ring commutes with
field-extension base change along an extension of discrete valuation rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.AffineBaseChange

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/- Lemma 62.4.3: if `R'/R` is an extension of discrete valuation rings inducing
fraction field extension `K'/K` and residue field extension `κ'/κ`, and `X` is
locally of finite type over `R`, then specialization of `r`-cycles on
`X' = X_{R'}` commutes with the field-extension base-change maps on generic
and special fibres. -/
@[stacks 0H4K] #check (AlgebraicGeometry.CycleGroup.cycleSpecialization_comp_baseChange :
  ∀
    {R R' : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (r : ℕ),
    ((toBase R R' f).cycleSpecialization r).comp (genericFiberBaseChange R R' f r) =
      (specialFiberBaseChange R R' f r).comp (f.cycleSpecialization r))

/- Specialization of an `r`-cycle on the generic fibre of `X / R`, then base
change to the special fibre of `X' / R'`, agrees with base change on the
generic fibre followed by specialization over `R'`. -/
#check (AlgebraicGeometry.CycleGroup.cycleSpecialization_baseChange :
  ∀
    {R R' : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
    (toBase R R' f).cycleSpecialization r (genericFiberBaseChange R R' f r α) =
      specialFiberBaseChange R R' f r (f.cycleSpecialization r α))

end AlgebraicGeometry.CycleGroup
