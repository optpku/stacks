/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus.Bound

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GeometricGenus

/- Lemma 53.18.5: if `C` is a proper curve over a field `k`, then its geometric genus is at
most the separable degree of its global-sections field times its degree-one cohomology
dimension over that field. -/
@[stacks 0CE5] #check
  (AlgebraicGeometry.GeometricGenus.ofCurve_le_finSepDegree_mul_structureSheafH1Finrank :
      ∀ {k : Type u} [Field k] (C : SchemeOverField k) [Curve C] [IsProper C.hom],
      -- Local instance justification (noncanonical choice): this algebra structure is derived from the explicit morphism C.hom and must not be globally registered.
      letI : Algebra k (Scheme.globalSectionsRing C.left) :=
        Scheme.Hom.globalSectionsAlgebra C.hom
      -- Local instance justification (noncanonical choice): this field structure is derived from the explicit morphism C.hom and must not be globally registered.
      letI : Field (Scheme.globalSectionsRing C.left) :=
        (Scheme.Hom.globalSectionsField C.hom : Field (Scheme.globalSectionsRing C.left))
      ofScheme C (topologicalKrullDim_eq_one C).le ≤
        Field.finSepDegree k (Scheme.globalSectionsRing C.left) *
          Scheme.Hom.cohomologyFinrank C.left.toSpecΓ
            (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1)

end AlgebraicGeometry.GeometricGenus
