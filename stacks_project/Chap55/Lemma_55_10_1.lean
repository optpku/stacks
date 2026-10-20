module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Uniqueness

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.10.1: A smooth projective curve of positive genus over the fraction field
of a discrete valuation ring, with no nonconstant global functions, has a minimal regular
model unique up to an isomorphism compatible with the chosen generic-fibre identification. -/
@[stacks 0C6B]
#check (AlgebraicGeometry.Scheme.Hom.exists_minimalModel_uniqueUpToIso :
    ∀
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 0 < SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections),
    ∃ M : RegularModel R K C, IsMinimalModel M.base ∧
      ∀ N : RegularModel R K C, IsMinimalModel N.base →
        ∃ e : Over.mk M.base ≅ Over.mk N.base,
          M.genericFiberIso.hom ≫
              (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map e.hom =
            N.genericFiberIso.hom)

end AlgebraicGeometry.Scheme.Hom
