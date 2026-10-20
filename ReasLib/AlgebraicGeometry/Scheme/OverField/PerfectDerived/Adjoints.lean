module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Representability
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- Every linear exact functor between the perfect derived categories of proper schemes over a
field, with regular source, has an exact right adjoint. -/
theorem hasExactRightAdjoint
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Scheme.Regular X.left]
    (F : PerfectDerived X ⥤ PerfectDerived Y) [F.Linear k]
    (h_exact : F.HasTriangulatedStructure) :
    ∃ (G : PerfectDerived Y ⥤ PerfectDerived X) (adj : F ⊣ G),
      G.HasTriangulatedStructure := sorry

/-- Every linear exact functor between the perfect derived categories of proper schemes over a
field, with regular source, has an exact left adjoint. -/
theorem hasExactLeftAdjoint
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Scheme.Regular X.left]
    (F : PerfectDerived X ⥤ PerfectDerived Y) [F.Linear k]
    (h_exact : F.HasTriangulatedStructure) :
    ∃ (H : PerfectDerived Y ⥤ PerfectDerived X) (adj : H ⊣ F),
      H.HasTriangulatedStructure := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
