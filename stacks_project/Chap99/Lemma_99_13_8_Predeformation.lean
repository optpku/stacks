module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.Predeformation

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Spaces

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS))

/- The predeformation projection of a finite-presentation, flat, proper residue object. -/
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.predeformationFunctor
  openImmersion kToS h_factor x :
  AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.Predeformation.Obj
    openImmersion kToS h_factor x ⥤ ArtinianLocalAlgCat Λ k)
