/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth

/-!
# Smooth morphisms of categories cofibered in groupoids

A morphism of categories cofibered in groupoids over `C_Λ` is smooth when it
satisfies the infinitesimal lifting property along surjections.
-/

@[expose] public section

open CategoryTheory

universe u v w v' w'

/- Definition 90.8.1: a morphism of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is smooth when it has compatible lifts along every
surjective base map. -/
@[stacks 06HG] #check (CategoryTheory.BasedFunctor.IsSmooth :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op],
    (X ⥤ᵇ Y) → Prop)
