module

public import Mathlib.CategoryTheory.Countable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence.Family
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField.PerfectDerived

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Over an algebraically closed field, there is a countable family of finite-type
bases carrying smooth proper pairs and perfect relative equivalence kernels such
that every pair of smooth proper schemes with linearly exact equivalent perfect
derived categories is realized by the two fibers at a common rational point. -/
theorem exists_countable_relativeEquivalenceFamily
    {K : Type u} [Field K] [IsAlgClosed K] :
    ∃ I : Type u, Countable I ∧
      ∃ F : I → FourierMukaiObject.RelativeEquivalenceFamily K,
        ∀ (X Y : SchemeOverField K)
          [IsProper X.hom] [Smooth X.hom] [IsProper Y.hom] [Smooth Y.hom]
          (Φ : PerfectDerived X ⥤ PerfectDerived Y)
          [Φ.Linear K] [Φ.IsEquivalence]
          (hΦ : Φ.HasTriangulatedStructure),
          ∃ (i : I) (s : SchemeOverField.point K ⟶ (F i).base),
            Nonempty (X ≅ (F i).fiberX s) ∧
              Nonempty (Y ≅ (F i).fiberY s) := sorry

end AlgebraicGeometry.SchemeOverField
