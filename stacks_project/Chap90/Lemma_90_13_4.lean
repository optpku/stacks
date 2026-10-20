module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]

/- Lemma 90.13.4: if `p` is a predeformation category satisfying Schlessinger's
conditions (S1) and (S2), and if the tangent space is finite-dimensional over
`k`, then `p` admits a versal formal object. -/
@[stacks 06IW] #check (CategoryTheory.Functor.exists_isVersal :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [CategoryTheory.Functor.IsPredeformationCategory p]
    [CategoryTheory.Functor.HasSchlessingerS1 p]
    [CategoryTheory.Functor.HasSchlessingerS2 p]
    [FiniteDimensional k
      ((CategoryTheory.Functor.fiberIsoClassFunctor p).obj
        (ArtinianLocalAlgCat.dualNumber Λ k))],
    ∃ ξ : FormalObject p, FormalObject.IsVersal ξ)
