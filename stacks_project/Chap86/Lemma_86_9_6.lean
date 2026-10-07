module

public import stacks_project.Chap86.Lemma_86_9_6_BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits

universe u

/- Lemma 86.9.6: let `S` be a scheme. Consider a cartesian square of algebraic spaces
over `S`. Assume `f : X ⟶ Y` is proper, flat, and of finite presentation. Let
`(ω, τ)` be a relative dualizing complex for `f`. Then `(L(g')^* ω, Lg^* τ)` is a
relative dualizing complex for `f'`. -/
@[stacks 0E6C]
#check (RelativeDualizingComplex.baseChange :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [Proper f'] [Flat f'] [FinitePresentation f']
    (sq : IsPullback g' f' f g) (C : RelativeDualizingComplex f)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex)],
    RelativeDualizingComplex f')
