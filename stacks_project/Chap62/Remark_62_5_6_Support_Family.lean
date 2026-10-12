/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers

/-!
# Families of cycles on scheme-theoretic fibres

The family type, fibrewise dimension function, and conversion to algebraic
cycles are provided by the shared mathematical owner.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}

#check (AlgebraicGeometry.Scheme.Hom.fiberCycleDimension :
  (f : X ⟶ S) → (s : S) → f.fiber s → ℤ)

#check (AlgebraicGeometry.Scheme.Hom.fiberCycleDimension_apply :
  ∀ (f : X ⟶ S) (s : S) (x : f.fiber s),
    fiberCycleDimension f s x =
      (f.fiberToSpecResidueField s).relativeDimensionFunction (fun _ ↦ 0) x)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers : (X ⟶ S) → ℤ → Type u)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.toAlgebraicCycle :
  CyclesOnFibers f r → (s : S) → AlgebraicCycle (f.fiber s) ℤ)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.toAlgebraicCycle_apply :
  ∀ (α : CyclesOnFibers f r) (s : S) (x : f.fiber s),
    CyclesOnFibers.toAlgebraicCycle α s x =
      CycleGroup.toAlgebraicCycle (f.fiberCycleDimension s) r (α s) x)

end AlgebraicGeometry.Scheme.Hom
