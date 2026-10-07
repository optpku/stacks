module

public import Mathlib.CategoryTheory.Countable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap57.Lemma_57_17_5_Family
public import stacks_project.Chap57.Theorem_57_6_3_PerfectDerived

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

universe u

/-- Lemma 57.17.5: over an algebraically closed field `K` there is a countable
family of finite-type `K`-schemes `Sᵢ` with smooth proper morphisms `Xᵢ → Sᵢ`,
`Yᵢ → Sᵢ` and a perfect Fourier--Mukai kernel of a relative equivalence over
`Sᵢ`, such that every pair of smooth proper `K`-schemes with a `K`-linear exact
equivalence of `PerfectDerived` arises as `K`-fibers `(Xᵢ)ₛ` and `(Yᵢ)ₛ`. -/
@[stacks 0G0Y]
theorem exists_countable_relativeEquivalenceFamily
    {K : Type u} [Field K] [IsAlgClosed K] :
    ∃ I : Type u, Countable I ∧
      ∃ F : I → FourierMukaiObject.RelativeEquivalenceFamily K,
        ∀ (X Y : SchemeOverField K)
          [IsProper X.hom] [Smooth X.hom] [IsProper Y.hom] [Smooth Y.hom]
          (Φ : PerfectDerived X ⥤ PerfectDerived Y)
          [Φ.Linear K] [Φ.CommShift ℤ] [Φ.IsEquivalence]
          (hΦ : Φ.HasTriangulatedStructure),
          ∃ (i : I) (s : SchemeOverField.point K ⟶ (F i).base),
            Nonempty (X ≅ (F i).fiberX s) ∧
              Nonempty (Y ≅ (F i).fiberY s) := sorry
