module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Restriction

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
  [AlgebraicGeometry.Flat hX]
  (U : X.Opens)

/- The reusable implementation is owned by
`ReasLib.AlgebraicGeometry.FormalDeformation.Restriction`.
-/

#check (FlatSchemeCat.restrictFunctor Λ k
  X hX U :
  FlatSchemeCat.deformationCategory Λ k X hX ⥤
    FlatSchemeCat.deformationCategory Λ k U.toScheme (U.ι ≫ hX))

end
