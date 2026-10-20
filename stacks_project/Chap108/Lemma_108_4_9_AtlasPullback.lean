/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_Atlas

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
  (V : Over S) (q : yoneda.obj V ⟶ X.functorOfPoints)

/-- Actual represented pullback of the input atlas to a test scheme. -/
noncomputable def atlasPullback : Over S := (atlasMapEtale X).rep.pullback q

/-- The projection to the original test scheme. -/
noncomputable def atlasPullbackToSource : atlasPullback X V q ⟶ V :=
  (atlasMapEtale X).rep.snd q

/-- The projection to the atlas scheme. -/
noncomputable def atlasPullbackToAtlas : atlasPullback X V q ⟶ atlasScheme X :=
  (atlasMapEtale X).rep.fst' q

/-- The projection to the test scheme is etale by the input atlas property. -/
theorem atlasPullbackToSourceEtale : AlgebraicGeometry.Etale (atlasPullbackToSource X V q).left :=
  (atlasMapEtale X).property_snd q

/-- The actual represented projections form a pullback of the two original maps. -/
theorem atlasPullbackSquare :
    IsPullback (yoneda.map (atlasPullbackToAtlas X V q))
      (yoneda.map (atlasPullbackToSource X V q)) (atlasMap X) q :=
  (atlasMapEtale X).rep.isPullback' q

/-- The projection covers the test scheme, proved directly from local surjectivity
of the input atlas and the actual pullback's lifting property. -/
theorem atlasPullbackCover :
    Sieve.generate (Presieve.singleton (atlasPullbackToSource X V q)) ∈
      (Scheme.etaleTopology.over S) V := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := atlasMapSurjective X
  apply (Scheme.etaleTopology.over S).superset_covering _
    (Presheaf.imageSieve_mem (Scheme.etaleTopology.over S) (atlasMap X)
      (yonedaEquiv q))
  intro W f hf
  obtain ⟨t, ht⟩ := hf
  have e : yoneda.map t ≫ atlasMap X = yoneda.map f ≫ q := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using
      ht.trans (yonedaEquiv_naturality q f)
  let lift := (atlasMapEtale X).rep.lift (yoneda.map t) f e
  have fac : lift ≫ atlasPullbackToSource X V q = f :=
    (atlasMapEtale X).rep.lift_snd (yoneda.map t) f e
  rw [← fac]
  exact (Sieve.generate _).downward_closed
    (Sieve.le_generate _ _ _ (Presieve.singleton_self _)) lift

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
