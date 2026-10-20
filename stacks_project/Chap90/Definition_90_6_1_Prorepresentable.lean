module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable

/-!
# Prorepresentable functors on Artinian local algebras

A covariant `Type`-valued functor on `ArtinianLocalAlgCat` is prorepresentable when it is
isomorphic to the restriction of `coyoneda.obj (op R)` along the inclusion into
`CompleteLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-! The migrated declarations remain available through the ReasLib owner. -/
#check (ArtinianLocalAlgCat.inclusion : ArtinianLocalAlgCat Λ k ⥤ CompleteLocalAlgCat Λ k)
#check (CompleteLocalAlgCat.restrictedCoyoneda : CompleteLocalAlgCat Λ k →
  ArtinianLocalAlgCat Λ k ⥤ Type u)
#check (CategoryTheory.Functor.IsProrepresentable : (ArtinianLocalAlgCat Λ k ⥤ Type u) → Prop)
