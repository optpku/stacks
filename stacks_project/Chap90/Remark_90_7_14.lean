module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable.Hom
import StacksCheckRecall

@[expose] public section

open CategoryTheory FormalObject CompleteLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Remark 90.7.14 -/
@[stacks 06HD] #check (FormalObject.fromProrepresentableHom_isEquivalence :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (U : ArtinianLocalAlgCat Λ k ⥤ Type u) (R : CompleteLocalAlgCat Λ k)
    (e : U ≅ restrictedCoyoneda R),
    (FormalObject.fromProrepresentableHom p e).IsEquivalence)
