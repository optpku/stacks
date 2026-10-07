module

public import stacks_project.Chap61.Lemma_61_19_7_Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.19.7

The first cohomology sets of torsor isomorphism classes on the small étale
and small pro-étale sites of a scheme agree after inverse image along
`etaleToProEt`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ GrpCat.{u + 1}, (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]
variable [HasWeakSheafify (ProEt.topology X) GrpCat.{u + 1}]
variable [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget GrpCat.{u + 1})]
variable [(ProEt.topology X).HasSheafCompose (CategoryTheory.forget GrpCat.{u + 1})]
variable [(CategoryTheory.forget GrpCat.{u + 1}).PreservesLeftKanExtensions (etaleToProEt X).op]
variable [(ProEt.topology X).PreservesSheafification (CategoryTheory.forget GrpCat.{u + 1})]
variable [PreservesFiniteLimits (etaleToProEtPullback X (Type (u + 1)))]

/-- Lemma 61.19.7: for a scheme `X` and a sheaf `G` of possibly noncommutative
groups on `X.Etale`, the canonical comparison of first cohomology sets
`Torsor.IsoClasses G → Torsor.IsoClasses ((etaleToProEtPullback X GrpCat.{u + 1}).obj G)`
is bijective. Here `Torsor.IsoClasses` is the set of isomorphism classes of
torsors from Cohomology on Sites, Section 21.4, and
`(etaleToProEtPullback X GrpCat.{u + 1}).obj G` is the inverse image `ε⁻¹ G`
along the étale-to-pro-étale comparison of small sites. -/
@[stacks 099X]
theorem etaleToProEt_torsorIsoClasses_bijective
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) :
    Function.Bijective (etaleToProEt_torsorIsoClasses X G) :=
  sorry

end AlgebraicGeometry.Scheme
