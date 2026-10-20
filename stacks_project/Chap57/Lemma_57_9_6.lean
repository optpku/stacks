module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor.Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

universe u

/- Lemma 57.9.6: if `k` is a field and `f : X ⟶ Spec (CommRingCat.of k)` is a
quasi-compact separated smooth morphism, then there exist finite locally free
`X.Modules` `E` and `G` such that the diagonal module
`singleFunctor 0 (pushforwardStructureModule (pullback.diagonal f))` lies in
`⟨singleFunctor 0 (externalTensorProduct f f E G)⟩` in
`D((pullback f f).Modules)`. -/
@[stacks 0FZ5]
#check (AlgebraicGeometry.Scheme.Modules.exists_externalTensorProduct_mem_generated :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsSeparated f] [Smooth f],
    ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
      (G : X.Modules) (_ : G.IsFiniteLocallyFree),
      ObjectProperty.Generated.property
        ((DerivedCategory.singleFunctor ((Limits.pullback f f).Modules) 0).obj
          (AlgebraicGeometry.Scheme.Modules.externalTensorProduct f f E G))
        ((DerivedCategory.singleFunctor ((Limits.pullback f f).Modules) 0).obj
          (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))))
