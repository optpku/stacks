module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion.Continuity
import StacksCheckRecall

/-!
# Limit-preserving functors recover from the completion of their restriction

If `G : CompleteLocalAlgCat Λ k ⥤ Type w` commutes with limits, the unit
`typesCompletionUnit.app G` is an isomorphism. Representable functors are the
standard example.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.11 (1): if `G : CompleteLocalAlgCat Λ k ⥤ Type w` commutes with
limits, then the unit `typesCompletionUnit.app G` is an isomorphism. -/
@[stacks 06HE] #check (CategoryTheory.Functor.typesCompletionUnit_isIso :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (G : CompleteLocalAlgCat Λ k ⥤ Type w)
    [PreservesLimits G], IsIso (CategoryTheory.Functor.typesCompletionUnit.app G))

/- Remark 90.7.11 (2): if `R : CompleteLocalAlgCat Λ k`, then
`typesCompletionUnit.app (coyoneda.obj (op R))` is an isomorphism. -/
@[stacks 06HE] #check (CategoryTheory.Functor.coyoneda_typesCompletionUnit_isIso :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (R : CompleteLocalAlgCat Λ k),
    IsIso (CategoryTheory.Functor.typesCompletionUnit.app
      (CategoryTheory.coyoneda.obj (op R))))
