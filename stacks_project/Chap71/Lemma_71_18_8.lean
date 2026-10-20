/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap71.Lemma_71_16_4_Quotient
public import stacks_project.Chap71.Lemma_71_18_7_Blowup

/-!
# Exactness of strict transforms of algebraic-space modules

A quasicoherent short exact sequence on an algebraic space that remains exact
after every base change of the base remains exact after strict transform along
a blowup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The strict-transform functor of module sheaves preserves zero morphisms. -/
instance strictTransformFunctor_preservesZeroMorphisms
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B) :
    (strictTransformFunctor b E f).PreservesZeroMorphisms :=
  sorry

/-- Lemma 71.18.8: in the situation of Definition 71.18.1, if
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is a short exact sequence of quasi-coherent sheaves
on `X` that remains exact after any base change `T ⟶ B`, then the strict
transforms `F'ᵢ` relative to any blowup `B' ⟶ B` again form a short exact
sequence `0 ⟶ F'₁ ⟶ F'₂ ⟶ F'₃ ⟶ 0`. -/
@[stacks 0869]
theorem strictTransform_shortExact_of_forall_pullback_shortExact
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (f : X ⟶ B) (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hbase :
      ∀ {T : AlgebraicSpace S} (t : T ⟶ B),
        (C.map (Modules.pullback (pullback.fst f t))).ShortExact) :
    (C.map (strictTransformFunctor b (Z.inverseImage b) f)).ShortExact :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
