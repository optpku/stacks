/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Curve
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (X : SchemeOverField k) [IsProper X.hom]

#check (inferInstance : IsProper (FieldExtension.toBase k K X.hom))

/- Lemma 53.8.2: after extending the ground field from `k` to `K`, a proper
one-dimensional scheme with ground-field global functions retains these properties and its genus. -/
@[stacks 0BY9]
  #check
    (AlgebraicGeometry.SchemeOverField.baseChange_topologicalKrullDim_eq_one (X := X) (K := K) :
      topologicalKrullDim X.left = 1 →
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) →
          topologicalKrullDim (FieldExtension.baseChange k K X.hom) = 1)

#check
  (AlgebraicGeometry.SchemeOverField.baseChange_globalSectionsMap_bijective (X := X) (K := K) :
    topologicalKrullDim X.left = 1 →
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) →
        Function.Bijective
          (Scheme.Hom.globalSectionsMap (FieldExtension.toBase k K X.hom)))

#check
  (AlgebraicGeometry.SchemeOverField.baseChange_genus_eq (X := X) (K := K) :
    topologicalKrullDim X.left = 1 →
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) →
        Scheme.Hom.cohomologyFinrank (FieldExtension.toBase k K X.hom)
            (SheafOfModules.unit
              (FieldExtension.baseChange k K X.hom).ringCatSheaf :
                (FieldExtension.baseChange k K X.hom).Modules) 1 =
          Scheme.Hom.cohomologyFinrank X.hom
            (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)

end AlgebraicGeometry.SchemeOverField
