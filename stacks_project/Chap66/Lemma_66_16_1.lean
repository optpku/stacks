/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleFromScheme

/-!
# Permanence of étale morphisms from schemes to an algebraic space

Étale morphisms from schemes to an algebraic space are stable under composition with étale
scheme maps, cancel in commuting triangles, and descend along surjective étale scheme maps.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MorphismProperty

/- Lemma 66.16.1 (1): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`U`, `U'` be schemes over `S`. If `f : U ⟶ U'` is étale and `φ' : U' ⟶ X` is étale, then
the composition `U ⟶ X` is étale. -/
@[stacks 03EC] #check
  (AlgebraicGeometry.AlgebraicSpace.etale_comp :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U U' : Over S}
      (f : U ⟶ U') [Etale f.left]
      (φ' : yoneda.obj U' ⟶ X.functorOfPoints),
      (over (@Etale)).presheaf φ' →
      (over (@Etale)).presheaf (yoneda.map f ≫ φ'))

/- Lemma 66.16.1 (2): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`U`, `U'` be schemes over `S`. If `φ : U ⟶ X` and `φ' : U' ⟶ X` are étale and
`f : U ⟶ U'` is a morphism of schemes over `S` with `φ = φ' ∘ f`, then `f` is étale. -/
@[stacks 03EC] #check
  (AlgebraicGeometry.AlgebraicSpace.etale_of_comp :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U U' : Over S}
      (φ : yoneda.obj U ⟶ X.functorOfPoints)
      (φ' : yoneda.obj U' ⟶ X.functorOfPoints) (f : U ⟶ U'),
      (over (@Etale)).presheaf φ →
      (over (@Etale)).presheaf φ' →
      φ = yoneda.map f ≫ φ' → Etale f.left)

/- Lemma 66.16.1 (3): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`U`, `U'` be schemes over `S`. If `f : U ⟶ U'` is a surjective étale morphism of schemes and
`φ' : U' ⟶ X` is a morphism such that `φ' ∘ f` is étale, then `φ'` is étale. -/
@[stacks 03EC] #check
  (AlgebraicGeometry.AlgebraicSpace.etale_of_surjective_etale :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U U' : Over S}
      (f : U ⟶ U') [Surjective f.left] [Etale f.left]
      (φ' : yoneda.obj U' ⟶ X.functorOfPoints),
      (over (@Etale)).presheaf (yoneda.map f ≫ φ') →
      (over (@Etale)).presheaf φ')
