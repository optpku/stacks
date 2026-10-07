module

public import stacks_project.Chap79.Lemma_79_9_7_Translation
import stacks_project.Chap79.Situation_79_9_2_OnField
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidAlgebraicSpace

noncomputable section

universe u

/- Lemma 79.9.7 (1): In Situation 79.9.2, if r : G.U ⟶ G.R is such that
r ≫ G.s and r ≫ G.t are automorphisms of Spec(.of k), then
G.leftTranslationAt r is an automorphism of G.R. -/
@[stacks 06E3] #check
  fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
      (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] [IsIso (r ≫ G.t)] ↦
    (inferInstance : IsIso (G.leftTranslationAt r))

/- Lemma 79.9.7 (2): In Situation 79.9.2, G.leftTranslationAt r sends the
identity section G.e to G.sourceSection r, which recovers r via
G.sourceSection_comp after the automorphism r ≫ G.s. -/
@[stacks 06E3] #check
  fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
      (r : G.U ⟶ G.R) [IsIso (r ≫ G.s)] ↦
    G.leftTranslationAt_mapsIdentity r
