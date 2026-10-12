/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Lemma_86_9_3_Uniqueness
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory

universe u

/- Lemma 86.9.3: let `S` be a scheme. Let `X ⟶ Y` be a proper, flat morphism of
algebraic spaces which is of finite presentation. If `(ωⱼ, τⱼ)`, `j = 1, 2` are two
relative dualizing complexes on `X / Y`, then there is a unique isomorphism
`(ω₁, τ₁) ⟶ (ω₂, τ₂)`. -/
@[stacks 0E5Z] #check (RelativeDualizingComplex.existsUniqueIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      [Proper f] [Flat f] [FinitePresentation f]
      (C D : RelativeDualizingComplex f),
      ∃! e : C.complex ≅ D.complex,
        C.trace = (moduleDerivedPushforward f).map e.hom ≫ D.trace)
