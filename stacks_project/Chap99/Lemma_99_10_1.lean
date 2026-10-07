module

public import stacks_project.Chap99.Lemma_99_10_1_Picard
public import stacks_project.Chap99.Lemma_99_10_1_Inclusion

/-!
# Lemma 99.10.1

The natural map from the Picard category of a flat, finitely presented, proper
morphism of algebraic spaces to the category of coherent sheaves is
representable by open immersions: invertibility of a coherent module on a
fibre is cut out by an open subscheme of the test scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Picard
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.10.1: let `S` be a scheme, and let `f : X ⟶ B` be a morphism of
algebraic spaces over `S` which is flat, of finite presentation, and proper.
The natural map `toCoh f : Pic_{X/B} ⟶ Coh_{X/B}` is representable by open
immersions. Equivalently, for every object `(T, g, F)` of `CohStack.Obj f`
there is an open subscheme `U ⊂ T` such that a morphism of schemes `T' ⟶ T`
over `B` factors through `U` if and only if the pullback of `F` to `X_{T'}` is
invertible. -/
@[stacks 0D03]
theorem exists_opens_isInvertible_iff (f : X ⟶ B) [Flat f] [FinitePresentation f]
    [Proper f] (x : CohStack.Obj f) :
    ∃ U : (x.σ.left.left).Opens,
      ∀ {τ : CohStack.SchemesOver B} (h : τ ⟶ x.σ),
        Nonempty (Over.mk h.left.left ⟶ Over.mk U.ι) ↔
          isInvertibleObject
            ((Modules.pullback (CohStack.fiberMap f h)).obj x.module) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
