module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Countable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap57.Theorem_57_6_3_PerfectDerived

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

universe u

/-- Theorem 57.18.2: over an algebraically closed field `K`, a fixed smooth proper
`K`-scheme `X` has at most countably many isomorphism classes of smooth proper
`K`-schemes `Y` admitting a `K`-linear exact equivalence of `PerfectDerived`. -/
@[stacks 0G11]
theorem countable_isoClasses_of_derivedEquivalent_smoothProper
    {K : Type u} [Field K] [IsAlgClosed K]
    (X : SchemeOverField K) [IsProper X.hom] [Smooth X.hom] :
    ∃ I : Type u, Countable I ∧
      ∃ Yᵢ : I → SchemeOverField K,
        (∀ i, IsProper (Yᵢ i).hom ∧ Smooth (Yᵢ i).hom) ∧
          ∀ (Y : SchemeOverField K) [IsProper Y.hom] [Smooth Y.hom]
            (Φ : PerfectDerived X ⥤ PerfectDerived Y)
            [Φ.Linear K] [Φ.CommShift ℤ] [Φ.IsEquivalence],
            Φ.HasTriangulatedStructure →
              ∃ i : I, Nonempty (Y ≅ Yᵢ i) := sorry
