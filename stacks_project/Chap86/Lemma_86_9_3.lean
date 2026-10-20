module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory

universe u

/- Lemma 86.9.3: let `S` be a scheme. Let `X ⟶ Y` be a proper, flat morphism of
algebraic spaces which is of finite presentation. If `(ωⱼ, τⱼ)`, `j = 1, 2` are two
relative dualizing complexes on `X / Y`, then there is a unique isomorphism
`(ω₁, τ₁) ⟶ (ω₂, τ₂)`. -/
@[stacks 0E5Z] #check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.existsUniqueIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      [Proper f] [Flat f] [FinitePresentation f]
      (C D : RelativeDualizingComplex f),
      ∃! e : C.complex ≅ D.complex,
        C.trace = (moduleDerivedPushforward f).map e.hom ≫ D.trace)
