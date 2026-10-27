/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Category
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent
public import ReasLib.CategoryTheory.Functor.Exactness.ShortExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/-
Source correction (Stacks 06ZA): the original claim says that, for every injective
module-valued functor I and every short exact sequence of B-modules, the tangent
sequence TI(B, N₁) → TI(B, N) → TI(B, N₂) → 0 is exact. This claim is false.
The free-module equalizer argument in its proof overlooks cancellation between
distinct basis maps with the same restriction. The counterstatement below records
failure of exactness at the middle term; it does not certify the original lemma.
-/

/-- An injective module-valued functor can have a tangent functor that fails to
preserve exactness of a short exact complex.

Take `k = F₂`, `E = k[e]/(e²)` and `J = Hom_k(E, k)`, with action
`(a • j)(b) = j(ab)`. The adjunction `Hom_E(M, J) ≃ Hom_k(M, k)` makes `J`
injective. Define `I(X) = ∏ (φ : X → E), J`, with the `X`-action on the
`φ`-coordinate restricted along `φ`, and transition maps given by precomposition.
This coinduction is right adjoint to evaluation at `E`; since evaluation preserves
monomorphisms, `I` is categorically injective.

At `A = B = k`, use the split complex `k → k² → k`, with inclusion into the
first coordinate and projection onto the second. The four algebra maps
`k[x,y]/(x,y)² → E` are indexed by `00, 01, 10, 11`. The tangent middle term
consists of tuples `(0,a,b,c)` in `J⁴`. Its two maps are
`j ↦ (0,0,j,j)` and `(0,a,b,c) ↦ a`. For `j ≠ 0`, the tuple `(0,0,j,0)`
lies in the kernel but outside the image. Lifting the finite rings and modules
to `Type u` gives the example in every displayed universe: each hom index and
each individual product is `u`-small. No ambient enough-injectives assertion is
needed.

The single proof debt is the Lean formalization of this construction and
calculation. This existential proposition supplies no chosen data, and is a
correction to the false source statement, not a proof or coverage of 06ZA. -/
theorem exists_injective_tangent_not_exact :
    ∃ (A : CommRingCat.{u}) (I : ModuleValuedFunctor.{u, u} A),
      IsInjective I ∧
        ∃ (B : Under A) (S : ShortComplex (ModuleCat.{u} B.right)),
          S.ShortExact ∧
            ¬ (ComposableArrows.mk₂ ((I.tangent.fixedBase B).map S.f)
              ((I.tangent.fixedBase B).map S.g)).Exact := sorry

end ModuleValuedFunctor
