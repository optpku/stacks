/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence.Countable
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

universe u

/- Lemma 57.17.5: over an algebraically closed field `K` there is a countable
family of finite-type `K`-schemes `Sᵢ` with smooth proper morphisms `Xᵢ → Sᵢ`,
`Yᵢ → Sᵢ` and a perfect Fourier--Mukai kernel of a relative equivalence over
`Sᵢ`, such that every pair of smooth proper `K`-schemes with a `K`-linear exact
equivalence of `PerfectDerived` arises as `K`-fibers `(Xᵢ)ₛ` and `(Yᵢ)ₛ`. -/
@[stacks 0G0Y] #check
  (AlgebraicGeometry.SchemeOverField.exists_countable_relativeEquivalenceFamily :
    ∀ {K : Type u} [Field K] [IsAlgClosed K],
    ∃ I : Type u, Countable I ∧
      ∃ F : I → FourierMukaiObject.RelativeEquivalenceFamily K,
        ∀ (X Y : SchemeOverField K)
          [IsProper X.hom] [Smooth X.hom] [IsProper Y.hom] [Smooth Y.hom]
          (Φ : PerfectDerived X ⥤ PerfectDerived Y)
          [Φ.Linear K] [Φ.IsEquivalence]
          (hΦ : Φ.HasTriangulatedStructure),
          ∃ (i : I) (s : SchemeOverField.point K ⟶ (F i).base),
            Nonempty (X ≅ (F i).fiberX s) ∧
              Nonempty (Y ≅ (F i).fiberY s))
