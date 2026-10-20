module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.SmallestDescent.Versal
import StacksCheckRecall

/-!
# Lemma 90.14.3

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and has (S1),
`ξ` is a versal formal object, and `f : ξ' ⟶ ξ` is a smallest descent morphism
as in Lemma 90.14.2, then `f.base` exhibits `ξ.base` as a finite-variable power
series ring over `ξ'.base`, and `ξ'` is versal.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.14.3 (1): if `p` is cofibered in groupoids and has (S1), `ξ` is a
versal formal object, and `f : ξ' ⟶ ξ` is a smallest descent morphism as in
Lemma 90.14.2, then `f.base` exhibits `ξ.base` as a finite-variable power
series ring over `ξ'.base`. -/
@[stacks 06T3] #check (FormalObject.Hom.IsSmallestDescent.isPowerSeriesOver :
  ∀ [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {ξ ξ' : FormalObject p} [FormalObject.IsVersal ξ] {f : ξ' ⟶ ξ},
    FormalObject.Hom.IsSmallestDescent f → CompleteLocalAlgCat.IsPowerSeriesOver f.base)

/- Lemma 90.14.3 (2): if `p` is cofibered in groupoids and has (S1), `ξ` is a
versal formal object, and `f : ξ' ⟶ ξ` is a smallest descent morphism as in
Lemma 90.14.2, then `ξ'` is versal. -/
@[stacks 06T3] #check (FormalObject.Hom.IsSmallestDescent.isVersal :
  ∀ [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {ξ ξ' : FormalObject p} [FormalObject.IsVersal ξ] {f : ξ' ⟶ ξ},
    FormalObject.Hom.IsSmallestDescent f → FormalObject.IsVersal ξ')
