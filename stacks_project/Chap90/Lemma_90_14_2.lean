module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.SmallestDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.14.2: a versal formal object of a category cofibered in groupoids
satisfying (S1) admits a smallest descent over a subring, with minimal Artinian
test pushforwards and surjective incoming complete local base maps. -/
@[stacks 06T2] #check (FormalObject.exists_isSmallestDescent :
  ∀ [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    ∃ (ξ' : FormalObject p) (f : ξ' ⟶ ξ), FormalObject.Hom.IsSmallestDescent f)
