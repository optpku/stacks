/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_21_4_Functors
public import stacks_project.Chap90.Lemma_90_4_3
import StacksCheckRecall

/-!
# Representable groupoids in functors, coyoneda presentation

A representable groupoid in functors on `C` is presented by objects and morphisms
of `C`. The pushout is required so that composition is a morphism of `C`; on
`CompleteLocalAlgCat Λ k` this is automatic.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- Remark 90.21.5 (1): a representable groupoid in functors on `C` is given by
objects `U` and `R` of `C` and morphisms `s, t : U ⟶ R` and `c : R ⟶ pushout s t`
such that the coyoneda quintuple
`(coyoneda.obj (op U), coyoneda.obj (op R), coyoneda.map (op s), coyoneda.map (op t),
coyonedaComp s t c)` satisfies the condition of Definition 90.21.1. -/
@[stacks 06K7]
theorem exists_coyoneda_presentation (G : GroupoidInFunctors.{u, v, v} C)
    [IsRepresentable G] :
    ∃ (U R : C) (s t : U ⟶ R) (h : HasPushout s t)
      (c : R ⟶ @pushout C _ U R R s t h)
      (e : coyoneda.obj (op U) ⟶ coyoneda.obj (op R))
      (i : coyoneda.obj (op R) ⟶ coyoneda.obj (op R))
      (laws : @CoyonedaGroupoidLaws C _ U R s t h c e i),
      Nonempty (Iso (@ofCoyoneda C _ U R s t h c e i laws) G) :=
  sorry

/-- Remark 90.21.5 (2): the reason for requiring the existence of the pushout
`pushout s t` is so that the composition morphism `c` is defined at the level of
morphisms in `C`. Functor-level composition is exactly `coyonedaComp s t` of an
object-level morphism `c : R ⟶ pushout s t`. -/
@[stacks 06K7]
theorem coyonedaComp_bijective {U R : C} (s t : U ⟶ R) [HasPushout s t] :
    Function.Bijective (coyonedaComp s t) :=
  sorry

/-- There is a unique morphism `c : R ⟶ pushout s t` inducing a given functor-level
composition via `coyonedaComp`. -/
theorem existsUnique_coyonedaComp {U R : C} (s t : U ⟶ R) [HasPushout s t]
    (cFun : pullback (coyoneda.map (op s)) (coyoneda.map (op t)) ⟶ coyoneda.obj (op R)) :
    ∃! c : R ⟶ pushout s t, coyonedaComp s t c = cFun :=
  sorry

end CategoryTheory.GroupoidInFunctors

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.21.5 (3): this pushout requirement is always satisfied for representable
groupoids in functors on `CompleteLocalAlgCat Λ k`, since by Lemma 90.4.3 that
category admits pushouts. -/
@[stacks 06K7]
#check (CompleteLocalAlgCat.hasPushouts : HasPushouts (CompleteLocalAlgCat Λ k))
