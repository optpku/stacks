/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.SchemeTheoreticDensity

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.24.4: if an open subscheme is scheme-theoretically dense on the generic fiber of a
finite-type morphism to an irreducible scheme, then it is scheme-theoretically dense on every
fiber over some nonempty open subscheme of the target. -/
@[stacks 0573]
#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_schemeTheoreticallyDense_fiber :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) →
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] → [IrreducibleSpace Y] →
      (U : X.Opens) →
      AlgebraicGeometry.schemeTheoreticallyDense
          ((f.fiberι (_root_.genericPoint Y)) ⁻¹ᵁ U) →
      ∃ V : Y.Opens, Nonempty V ∧
        ∀ y : Y, y ∈ V →
          AlgebraicGeometry.schemeTheoreticallyDense ((f.fiberι y) ⁻¹ᵁ U))
