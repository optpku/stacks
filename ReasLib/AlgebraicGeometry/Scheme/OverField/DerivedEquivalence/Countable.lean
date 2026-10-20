module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Countable.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField.PerfectDerived

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Over an algebraically closed field, a fixed smooth proper scheme has at most
countably many isomorphism classes of smooth proper schemes admitting a linear
exact equivalence of perfect derived categories with it. -/
theorem countable_isoClasses_of_derivedEquivalent_smoothProper
    {K : Type u} [Field K] [IsAlgClosed K]
    (X : SchemeOverField K) [IsProper X.hom] [Smooth X.hom] :
    ∃ I : Type u, Countable I ∧
      ∃ Yᵢ : I → SchemeOverField K,
        (∀ i, IsProper (Yᵢ i).hom ∧ Smooth (Yᵢ i).hom) ∧
          ∀ (Y : SchemeOverField K) [IsProper Y.hom] [Smooth Y.hom]
            (Φ : PerfectDerived X ⥤ PerfectDerived Y)
            [Φ.Linear K] [Φ.IsEquivalence],
            Φ.HasTriangulatedStructure →
              ∃ i : I, Nonempty (Y ≅ Yᵢ i) := sorry

end AlgebraicGeometry.SchemeOverField
