module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

@[expose] public section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

attribute [instance] Hom.isLocalHom

/-- The carrier of an Artinian local algebra has its stored algebra structure. -/
instance instAlgebraCarrier (A : ArtinianLocalAlgCat Λ k) : Algebra Λ A.carrier :=
  A.algebra

/-- The carrier of an Artinian local algebra has its stored local-ring structure. -/
instance instIsLocalRingCarrier (A : ArtinianLocalAlgCat Λ k) : IsLocalRing A.carrier :=
  A.isLocalRing

/-- The carrier of an Artinian local algebra has its stored Artinian-ring structure. -/
instance instIsArtinianRingCarrier (A : ArtinianLocalAlgCat Λ k) : IsArtinianRing A.carrier :=
  A.isArtinianRing

end ArtinianLocalAlgCat
