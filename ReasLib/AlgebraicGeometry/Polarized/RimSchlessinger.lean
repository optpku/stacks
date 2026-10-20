module

public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
public import ReasLib.AlgebraicGeometry.Polarized.Pushout
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.RingTheory.Noetherian.ULift

/-!
# Rim–Schlessinger conditions for polarized proper schemes

Polarized proper schemes satisfy the strong Rim–Schlessinger condition, and their
predeformation functors satisfy the Rim–Schlessinger condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Polarized proper schemes over `Spec ℤ` satisfy the strong Rim–Schlessinger condition. -/
instance instHasStrongRimSchlessinger :
    HasStrongRimSchlessinger toGroupoidsOverSpecZ :=
  sorry

/-- The predeformation functor of a polarized proper scheme at a locally finite-type
field point, with a finite residue extension of a Noetherian affine chart, satisfies
the Rim–Schlessinger condition. -/
instance instHasRimSchlessinger_predeformationFunctor
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ specZ)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)) :
    Functor.HasRimSchlessinger
      (predeformationFunctor toGroupoidsOverSpecZ openImmersion kToS h_factor x) :=
  sorry

end AlgebraicGeometry.Polarized
