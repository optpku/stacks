module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Adjoints

import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 57.7.1 (1): for proper `k`-schemes `X` and `Y` with `X` regular, every
`k`-linear exact functor `F : PerfectDerived X ⥤ PerfectDerived Y` admits an
exact right adjoint. -/
@[stacks 0FYN] #check (AlgebraicGeometry.SchemeOverField.PerfectDerived.hasExactRightAdjoint :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k) [IsProper X.hom] [IsProper Y.hom]
      [Scheme.Regular X.left]
      (F : SchemeOverField.PerfectDerived X ⥤ SchemeOverField.PerfectDerived Y) [F.Linear k],
      F.HasTriangulatedStructure →
        ∃ (G : SchemeOverField.PerfectDerived Y ⥤ SchemeOverField.PerfectDerived X) (adj : F ⊣ G),
          G.HasTriangulatedStructure)

/- Lemma 57.7.1 (2): for proper `k`-schemes `X` and `Y` with `X` regular, every
`k`-linear exact functor `F : PerfectDerived X ⥤ PerfectDerived Y` admits an
exact left adjoint. -/
@[stacks 0FYN] #check (AlgebraicGeometry.SchemeOverField.PerfectDerived.hasExactLeftAdjoint :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k) [IsProper X.hom] [IsProper Y.hom]
      [Scheme.Regular X.left]
      (F : SchemeOverField.PerfectDerived X ⥤ SchemeOverField.PerfectDerived Y) [F.Linear k],
      F.HasTriangulatedStructure →
        ∃ (H : SchemeOverField.PerfectDerived Y ⥤ SchemeOverField.PerfectDerived X) (adj : H ⊣ F),
          H.HasTriangulatedStructure)

end
