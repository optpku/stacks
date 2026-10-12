/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective

/-!
# Checking universal injectivity after étale base change

A locally finite type morphism of algebraic spaces is universally injective as
soon as every étale base change is injective on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.UniversallyInjective

/-- Lemma 76.3.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type, and that for
every étale morphism `g : V ⟶ Y` the map `Points.map (pullback.snd f g)` is
injective. Then `f` is universally injective. -/
@[stacks 0AGE]
theorem of_locallyOfFiniteType_etale_pointsInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h_etale : ∀ {V : AlgebraicSpace S} (g : V ⟶ Y),
      Etale g → Function.Injective (Points.map (pullback.snd f g))) :
    UniversallyInjective f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UniversallyInjective
