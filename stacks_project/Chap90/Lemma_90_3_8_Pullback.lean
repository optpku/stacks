module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.CospanPullback

/-!
# Local and Artinian carriers of algebra pullbacks

The concrete algebra pullback and its two projections use the canonical
Artinian-local cospan instances.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A1 A2 : ArtinianLocalAlgCat Λ k}

#check (ArtinianLocalAlgCat.instIsLocalRing_cospanPullback :
  (f1 : A1 ⟶ A) → (f2 : A2 ⟶ A) → IsLocalRing (AlgHom.pullback f1.hom f2.hom))

#check (ArtinianLocalAlgCat.instIsArtinianRing_cospanPullback :
  (f1 : A1 ⟶ A) → (f2 : A2 ⟶ A) → IsArtinianRing (AlgHom.pullback f1.hom f2.hom))

#check (ArtinianLocalAlgCat.instIsLocalHom_cospanPullbackFst :
  (f1 : A1 ⟶ A) → (f2 : A2 ⟶ A) → IsLocalHom (AlgHom.pullbackFst f1.hom f2.hom))

#check (ArtinianLocalAlgCat.instIsLocalHom_cospanPullbackSnd :
  (f1 : A1 ⟶ A) → (f2 : A2 ⟶ A) → IsLocalHom (AlgHom.pullbackSnd f1.hom f2.hom))

end ArtinianLocalAlgCat
