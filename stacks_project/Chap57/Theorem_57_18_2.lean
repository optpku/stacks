/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DerivedEquivalence.Countable
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

universe u

/- Theorem 57.18.2: over an algebraically closed field `K`, a fixed smooth proper
`K`-scheme `X` has at most countably many isomorphism classes of smooth proper
`K`-schemes `Y` admitting a `K`-linear exact equivalence of `PerfectDerived`. -/
@[stacks 0G11] #check
  (AlgebraicGeometry.SchemeOverField.countable_isoClasses_of_derivedEquivalent_smoothProper :
    ∀ {K : Type u} [Field K] [IsAlgClosed K]
      (X : SchemeOverField K) [IsProper X.hom] [Smooth X.hom],
    ∃ I : Type u, Countable I ∧
      ∃ Yᵢ : I → SchemeOverField K,
        (∀ i, IsProper (Yᵢ i).hom ∧ Smooth (Yᵢ i).hom) ∧
          ∀ (Y : SchemeOverField K) [IsProper Y.hom] [Smooth Y.hom]
            (Φ : PerfectDerived X ⥤ PerfectDerived Y)
            [Φ.Linear K] [Φ.IsEquivalence],
            Φ.HasTriangulatedStructure →
              ∃ i : I, Nonempty (Y ≅ Yᵢ i))
