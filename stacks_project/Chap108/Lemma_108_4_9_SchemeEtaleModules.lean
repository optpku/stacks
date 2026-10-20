/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_DenseModuleSheaves
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

/-- A genuinely small affine-etale index category, from Mathlib's proved size bound. -/
abbrev SchemeAffineIndex (S : Scheme.{u}) := SmallModel S.AffineEtale

/-- The actual affine-etale inclusion from the proved small model. -/
noncomputable def schemeAffineInclusion (S : Scheme.{u}) : SchemeAffineIndex S ⥤ S.Etale :=
  (equivSmallModel S.AffineEtale).inverse ⋙ Scheme.AffineEtale.Spec S

/-- Pull back the affine-etale topology to its small model. -/
noncomputable def schemeAffineTopology (S : Scheme.{u}) : GrothendieckTopology (SchemeAffineIndex S) :=
  (equivSmallModel S.AffineEtale).inverse.inducedTopology (Scheme.AffineEtale.topology S)

/-- The dense small affine site certifies modules in the original, unlifted etale universe. -/
theorem schemeEtaleModulesGrothendieck (S : Scheme.{u})
    (R : Sheaf S.smallEtaleTopology RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  let G := (equivSmallModel S.AffineEtale).inverse
  let K := G.inducedTopology (Scheme.AffineEtale.topology S)
  let F := G ⋙ Scheme.AffineEtale.Spec S
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : G.IsContinuous K (Scheme.AffineEtale.topology S) := by
    dsimp [K, G]
    infer_instance
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : F.IsContinuous K S.smallEtaleTopology :=
    Functor.isContinuous_comp G (Scheme.AffineEtale.Spec S)
      K (Scheme.AffineEtale.topology S) S.smallEtaleTopology
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : (F.sheafPushforwardContinuous AddCommGrpCat.{u} K S.smallEtaleTopology).Faithful :=
    Functor.Faithful.of_iso (Functor.sheafPushforwardContinuousComp
      G (Scheme.AffineEtale.Spec S) AddCommGrpCat.{u}
      K (Scheme.AffineEtale.topology S) S.smallEtaleTopology)
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI : IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology S AddCommGrpCat.{u}
  exact denseModulesGrothendieck S.smallEtaleTopology R K F

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
