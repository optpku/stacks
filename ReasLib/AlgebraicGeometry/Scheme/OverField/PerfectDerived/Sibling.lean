module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.CoherentModule
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- Siblinghood of exact `k`-linear functors `PerfectDerived X ⥤ PerfectDerived Y` consists of
isomorphism on degree-`0` coherent modules and on every perfect object. -/
def areSiblings {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Scheme.Regular X.left] (F F' : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ]
    (hF : F.HasTriangulatedStructure) (hF' : F'.HasTriangulatedStructure) : Prop :=
  (∀ (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ],
      Nonempty (F.obj (ofCoherentModule X ℱ) ≅ F'.obj (ofCoherentModule X ℱ))) ∧
    ∀ K : PerfectDerived X, Nonempty (F.obj K ≅ F'.obj K)

/-- Siblinghood gives an isomorphism on every perfect object. -/
theorem areSiblings_obj {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Scheme.Regular X.left] (F F' : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ]
    (hF : F.HasTriangulatedStructure) (hF' : F'.HasTriangulatedStructure)
    (h : areSiblings F F' hF hF') (K : PerfectDerived X) :
    Nonempty (F.obj K ≅ F'.obj K) := sorry

/-- Siblinghood gives an isomorphism on the degree-`0` object of every coherent module. -/
theorem areSiblings_ofCoherent {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Scheme.Regular X.left] (F F' : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ]
    (hF : F.HasTriangulatedStructure) (hF' : F'.HasTriangulatedStructure)
    (h : areSiblings F F' hF hF') (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ] :
    Nonempty (F.obj (ofCoherentModule X ℱ) ≅ F'.obj (ofCoherentModule X ℱ)) := sorry

/-- Siblinghood is symmetric under exchanging the two functors. -/
theorem areSiblings_symm {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Scheme.Regular X.left] (F F' : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ]
    (hF : F.HasTriangulatedStructure) (hF' : F'.HasTriangulatedStructure)
    (h : areSiblings F F' hF hF') : areSiblings F' F hF' hF := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
