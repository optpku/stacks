module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Smooth
import StacksCheckRecall

/-!
# Smoothness after change of residue field

A smooth morphism of categories cofibered in groupoids over `C_{Λ, k}` remains
smooth after reindexing along a finite residue-field extension `k → l`.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

namespace ArtinianLocalAlgCat

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) (q : G ⥤ ArtinianLocalAlgCat Λ k)

variable [Functor.IsFibered.InGroupoids p.op] [Functor.IsFibered.InGroupoids q.op]
variable (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
variable [BasedFunctor.IsSmooth φ]

/- Lemma 90.29.5: A smooth morphism remains smooth after change of residue field. -/
@[stacks 07WD] #check (ArtinianLocalAlgCat.instIsSmooth_residueChangeOverBased Λ k l p q φ :
  BasedFunctor.IsSmooth (ArtinianLocalAlgCat.residueChangeOverBased Λ k l p q φ))

end ArtinianLocalAlgCat
