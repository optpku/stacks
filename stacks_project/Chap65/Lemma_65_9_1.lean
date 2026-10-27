/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AtlasCoequalizer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair

/-!
# Lemma 65.9.1

A surjective étale morphism from a scheme to an algebraic space has kernel pair an
étale equivalence relation, and is a coequalizer in the category of fppf sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 65.9.1 (1): `j : R ⟶ U ×_S U` defines an equivalence relation on `U` over `S`. -/
@[stacks 0262] #check (AlgebraicGeometry.AlgebraicSpace.isEquivalenceRelation :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {U : Over S} →
    (f : yoneda.obj U ⟶ F.functorOfPoints) →
      (h_etale : (MorphismProperty.over (@Etale)).presheaf f) →
        IsEquivalenceRelation (kernelPair f h_etale.rep).t (kernelPair f h_etale.rep).s)

/- Lemma 65.9.1 (2): the projections `s, t : R ⟶ U` are étale. -/
@[stacks 0262] #check (AlgebraicGeometry.AlgebraicSpace.etale_projections :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {U : Over S} →
    (f : yoneda.obj U ⟶ F.functorOfPoints) →
      (h_etale : (MorphismProperty.over (@Etale)).presheaf f) →
        Etale (kernelPair f h_etale.rep).t.left ∧ Etale (kernelPair f h_etale.rep).s.left)

/- Lemma 65.9.1 (3): `R ⇉ U ⟶ F` is a coequalizer diagram in `Sheaf ((Sch/S)_fppf)`. -/
@[stacks 0262] #check (AlgebraicGeometry.AlgebraicSpace.isCoequalizer :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {U : Over S} →
    (f : yoneda.obj U ⟶ F.functorOfPoints) →
      (h_etale : (MorphismProperty.over (@Etale)).presheaf f) →
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f →
          Nonempty (IsColimit (cofork f h_etale)))

end AlgebraicGeometry.AlgebraicSpace
