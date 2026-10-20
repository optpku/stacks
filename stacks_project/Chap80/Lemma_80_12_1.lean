/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 80.12.1: denote the common underlying category of `Sch_fppf` and
`Sch_étale` by `Sch_α` (see Topologies, Remark 34.11.1), recovered here as the
common `Over S` of `Scheme.etaleTopology` and `Scheme.fppfTopology`. Let `S` be a
scheme. Let `F : (Over S)ᵒᵖ ⥤ Type` be a presheaf that is a sheaf for the étale
topology, whose diagonal `Δ : F ⟶ F ⨯ F` is representable, and that admits `U`
over `S` with a map `U ⟶ F` which is surjective and étale. Then `F` is an
algebraic space in the sense of Algebraic Spaces, Definition 65.6.1. -/
@[stacks 076M] #check (AlgebraicGeometry.AlgebraicSpace.ofEtaleSheaf :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) F →
    yoneda.relativelyRepresentable (Limits.diag F) →
    ∀ {U : Over S} (p : yoneda.obj U ⟶ F),
      (over (@Etale ⊓ @Surjective)).presheaf p → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.ofEtaleSheaf_functorOfPoints :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p),
    (AlgebraicGeometry.AlgebraicSpace.ofEtaleSheaf hF hΔ p hp).functorOfPoints = F)

#check (AlgebraicGeometry.AlgebraicSpace.ofEtaleSheaf_spec :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p),
    let X := AlgebraicGeometry.AlgebraicSpace.ofEtaleSheaf hF hΔ p hp
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          (over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
