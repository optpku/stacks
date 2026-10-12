/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Sibling

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

#check (AlgebraicGeometry.SchemeOverField.PerfectDerived.areSiblings :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [Scheme.Regular X.left]
      (F F' : PerfectDerived X ⥤ PerfectDerived X)
      [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ],
      F.HasTriangulatedStructure → F'.HasTriangulatedStructure → Prop)

#check (AlgebraicGeometry.SchemeOverField.PerfectDerived.areSiblings_obj :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [Scheme.Regular X.left]
      (F F' : PerfectDerived X ⥤ PerfectDerived X)
      [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ]
      (hF : F.HasTriangulatedStructure) (hF' : F'.HasTriangulatedStructure)
      (h : areSiblings F F' hF hF') (K : PerfectDerived X),
      Nonempty (F.obj K ≅ F'.obj K))

#check (AlgebraicGeometry.SchemeOverField.PerfectDerived.areSiblings_ofCoherent :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [Scheme.Regular X.left]
      (F F' : PerfectDerived X ⥤ PerfectDerived X)
      [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ]
      (hF : F.HasTriangulatedStructure) (hF' : F'.HasTriangulatedStructure)
      (h : areSiblings F F' hF hF') (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ],
      Nonempty (F.obj (ofCoherentModule X ℱ) ≅ F'.obj (ofCoherentModule X ℱ)))

#check (AlgebraicGeometry.SchemeOverField.PerfectDerived.areSiblings_symm :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [Scheme.Regular X.left]
      (F F' : PerfectDerived X ⥤ PerfectDerived X)
      [F.Linear k] [F'.Linear k] [F.CommShift ℤ] [F'.CommShift ℤ]
      (hF : F.HasTriangulatedStructure) (hF' : F'.HasTriangulatedStructure)
      (h : areSiblings F F' hF hF'),
      areSiblings F' F hF' hF)

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
