/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 33.33.1: for a coherent module on a scheme proper over a field, its Euler
characteristic is the signed finite sum of the dimensions of its cohomology groups. -/
@[stacks 0BEJ] #check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (F : X.Modules) [F.IsCoherent], ℤ)

#check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic_def :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (F : X.Modules) [F.IsCoherent],
      AlgebraicGeometry.Scheme.Hom.eulerCharacteristic f F =
        ∑ᶠ i : ℕ,
          ((i : ℤ).negOnePow : ℤ) *
            (AlgebraicGeometry.Scheme.Hom.cohomologyFinrank f F i : ℤ))
