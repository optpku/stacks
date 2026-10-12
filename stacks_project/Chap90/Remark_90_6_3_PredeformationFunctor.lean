/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Functor

/-! # Predeformation functors -/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Typed compatibility checks for the reusable predeformation-functor API. -/
#check (CategoryTheory.Functor.IsPredeformationFunctor :
  (ArtinianLocalAlgCat Λ k ⥤ Type v) → Prop)

#check (CategoryTheory.Functor.instIsPredeformationFunctor :
  {F : ArtinianLocalAlgCat Λ k ⥤ Type v} →
    [Unique (F.obj (ArtinianLocalAlgCat.residue Λ k))] →
      CategoryTheory.Functor.IsPredeformationFunctor F)

#check (CategoryTheory.Functor.isPredeformationFunctor_iff :
  (F : ArtinianLocalAlgCat Λ k ⥤ Type v) →
    CategoryTheory.Functor.IsPredeformationFunctor F ↔
      Nonempty (Unique (F.obj (ArtinianLocalAlgCat.residue Λ k))))
