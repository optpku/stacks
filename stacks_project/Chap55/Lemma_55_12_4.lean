/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import stacks_project.Chap53.Definition_53_8_1_Genus
public import stacks_project.Chap55.Definition_55_8_4_MinimalModel
public import stacks_project.Chap55.Lemma_55_8_5_Model

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom
namespace RegularModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]

/-- Two regular models are isomorphic when an isomorphism over the discrete valuation ring
intertwines their chosen identifications of the generic fibre with the curve. -/
def Isomorphic (M N : RegularModel R K C) : Prop :=
  ∃ e : Over.mk M.base ≅ Over.mk N.base,
    M.genericFiberIso.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map e.hom =
      N.genericFiberIso.hom

/-- A marked isomorphism of regular models is exactly a slice isomorphism whose pullback
intertwines the chosen generic-fibre identifications. -/
theorem isomorphic_iff (M N : RegularModel R K C) :
    Isomorphic M N ↔
      ∃ e : Over.mk M.base ≅ Over.mk N.base,
        M.genericFiberIso.hom ≫
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map e.hom =
          N.genericFiberIso.hom := sorry

/-- Lemma 55.12.4: for a smooth projective genus-zero curve with constant global
functions, the existence of two non-isomorphic minimal models forces the special
fibre of every minimal model to be the projective line over the residue field. -/
@[stacks 0CDA]
theorem specialFiber_iso_projectiveLine_of_nonunique
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = 0)
    (h_nonunique : ∃ M N : RegularModel R K C,
      IsMinimalModel M.base ∧ IsMinimalModel N.base ∧ ¬ Isomorphic M N)
    (M : RegularModel R K C) [IsMinimalModel M.base] :
    Nonempty
      (Over.mk (M.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom ≅
        ProjectiveSpace.schemeOver
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) 1) := sorry

end RegularModel
end Scheme.Hom
end AlgebraicGeometry
