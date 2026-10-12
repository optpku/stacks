/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.33.2: for a proper scheme over a field, Euler characteristic is additive along a
short exact sequence of coherent modules. -/
@[stacks 08AA] #check
  (AlgebraicGeometry.Scheme.Hom.eulerCharacteristic_eq_add_of_shortExact :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} {S : ShortComplex X.Modules}
      [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent],
      (f : X ⟶ Spec (CommRingCat.of k)) → [IsProper f] → S.ShortExact →
        AlgebraicGeometry.Scheme.Hom.eulerCharacteristic f S.X₂ =
          AlgebraicGeometry.Scheme.Hom.eulerCharacteristic f S.X₁ +
            AlgebraicGeometry.Scheme.Hom.eulerCharacteristic f S.X₃)
