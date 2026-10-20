/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RepresentableProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 65.11.4: let `S` be a scheme, and let `F`, `G` be algebraic spaces over `S`.
Let `f : G ⟶ F` be a representable morphism, let `U` be a scheme over `S`, and let
`q : yoneda.obj U ⟶ F.functorOfPoints` be surjective and étale. Write `V` for the
represented fibre product `hf.pullback q`, so that `V ⟶ U` is `hf.snd q`. Let `P` be a
property of morphisms of schemes in the sense of Definition 65.5.1. Then `f` has
property `P` if and only if the scheme morphism `(hf.snd q).left` has property `P`. -/
@[stacks 02WZ] #check
  (AlgebraicGeometry.AlgebraicSpace.representableMorphismProperty_iff_atlas_snd :
    ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S}
      (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget Scheme.fppfPrecoverage] {f : G ⟶ F}
      (hf : yoneda.relativelyRepresentable f) {U : Over S}
      (q : yoneda.obj U ⟶ F.functorOfPoints)
      (hq_etale : (over (@Etale)).presheaf q)
      (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q),
      Scheme.representableMorphismProperty S P f ↔ P (hf.snd q).left)
