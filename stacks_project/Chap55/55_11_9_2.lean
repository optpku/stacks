/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus.Bound

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GeometricGenus

/- 55.11.9.2: the geometric genus is at most the separable-degree-weighted
cohomology dimension, which is at most the full-degree-weighted cohomology dimension. -/
@[stacks 0CEC] #check
  (AlgebraicGeometry.GeometricGenus.ofCurve_le_weightedGenus_chain :
    ∀ {k : Type u} [Field k] (C : SchemeOverField k) [Curve C] [IsProper C.hom],
    -- Local instance justification (noncanonical choice): the algebra action depends on C.hom, which is not recoverable from the global-sections carrier.
    letI : Algebra k (Scheme.globalSectionsRing C.left) :=
      Scheme.Hom.globalSectionsAlgebra C.hom
    -- Local instance justification (defeq pin): use the exact globalSectionsField C.hom structure appearing in the existing geometric-genus bound.
    letI : Field (Scheme.globalSectionsRing C.left) :=
      (Scheme.Hom.globalSectionsField C.hom : Field (Scheme.globalSectionsRing C.left))
    ofScheme C (topologicalKrullDim_eq_one C).le ≤
        Field.finSepDegree k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 ∧
      Field.finSepDegree k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 ≤
        Module.finrank k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1)

end AlgebraicGeometry.GeometricGenus
