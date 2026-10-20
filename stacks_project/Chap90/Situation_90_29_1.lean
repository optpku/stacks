module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Cofibered
import StacksCheckRecall

/-!
# Change of residue field

A finite tower `Λ → k → l` of fields induces the comparison functor
`C_{Λ, l} ⟶ C_{Λ, k}` sending `B` to `B ×_l k`. Reindexing a category cofibered
in groupoids over `C_{Λ, k}` along that functor yields `p_{l/k}` over `C_{Λ, l}`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

/- Situation 90.29.1 (1): the comparison functor C_{Λ, l} ⟶ C_{Λ, k} sends B to
B ×_l k. -/
@[stacks 07W8] #check (ArtinianLocalAlgCat.residueChangeFunctor Λ k l :
  ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k)

/- Situation 90.29.1 (2): a category cofibered in groupoids p : F ⥤ C_{Λ, k}
reindexes to p_{l/k} : F_{l/k} ⥤ C_{Λ, l}. -/
@[stacks 07W8] #check (ArtinianLocalAlgCat.residueChangeOver Λ k l p :
  ArtinianLocalAlgCat.residueChangeTotal Λ k l p ⥤ ArtinianLocalAlgCat Λ l)

variable [Functor.IsFibered.InGroupoids p.op]

#check (ArtinianLocalAlgCat.instIsFiberedInGroupoids_residueChangeOver Λ k l p :
  Functor.IsFibered.InGroupoids (ArtinianLocalAlgCat.residueChangeOver Λ k l p).op)

#check (ArtinianLocalAlgCat.residueChangeOver.fiberMk_isEquivalence Λ k l p :
  ∀ B : ArtinianLocalAlgCat Λ l,
    (ArtinianLocalAlgCat.residueChangeOver.fiberMk Λ k l p B).IsEquivalence)
