module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.GenusZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom
namespace RegularModel

/- Lemma 55.12.4: for a smooth projective genus-zero curve with constant global
functions, the existence of two non-isomorphic minimal models forces the special
fibre of every minimal model to be the projective line over the residue field. -/
@[stacks 0CDA] #check
  (AlgebraicGeometry.Scheme.Hom.RegularModel.specialFiber_iso_projectiveLine_of_nonunique :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = 0)
    (h_nonunique : ∃ M N : RegularModel R K C,
      IsMinimalModel M.base ∧ IsMinimalModel N.base ∧ ¬ Isomorphic M N)
    (M : RegularModel R K C) [IsMinimalModel M.base],
    Nonempty
      (Over.mk (M.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom ≅
        ProjectiveSpace.schemeOver
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) 1))

#check (AlgebraicGeometry.Scheme.Hom.RegularModel.Isomorphic :
  ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom],
    RegularModel R K C → RegularModel R K C → Prop)

#check (AlgebraicGeometry.Scheme.Hom.RegularModel.isomorphic_iff :
  ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (M N : RegularModel R K C),
    Isomorphic M N ↔
      ∃ e : Over.mk M.base ≅ Over.mk N.base,
        M.genericFiberIso.hom ≫
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map e.hom =
          N.genericFiberIso.hom)

end RegularModel
end Scheme.Hom
end AlgebraicGeometry
