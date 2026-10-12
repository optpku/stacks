/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_AtlasPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

/-- An etale-covering singleton of schemes over a base is surjective on points. -/
theorem surjective_of_etale_singleton_cover {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V)
    (hf : Sieve.generate (Presieve.singleton f) ∈ (Scheme.etaleTopology.over S) V) :
    AlgebraicGeometry.Surjective f.left := by
  obtain ⟨cov, hcov, hle⟩ := (Scheme.mem_overGrothendieckTopology
    (P := @AlgebraicGeometry.Etale) V _).1 hf
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := hcov
  constructor
  intro x
  obtain ⟨i, y, hy⟩ := cov.exists_eq x
  obtain ⟨Z, a, b, hb, hab⟩ := hle _ _ (show cov.toPresieveOver ((cov.f i).asOver S) from ⟨i⟩)
  cases hb
  refine ⟨a.left y, ?_⟩
  have eq := congrArg (fun k ↦ k.left y) hab
  exact eq.trans hy

/-- The represented atlas projection onto each test scheme is actually surjective. -/
theorem atlasPullbackToSourceSurjective {S : Scheme.{u}} (X : AlgebraicSpace S)
    (V : Over S) (q : yoneda.obj V ⟶ X.functorOfPoints) :
    AlgebraicGeometry.Surjective (atlasPullbackToSource X V q).left :=
  surjective_of_etale_singleton_cover _ (atlasPullbackCover X V q)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
