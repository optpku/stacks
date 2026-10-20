module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Predeformation

/-! The coherent-sheaf predeformation projection at a residue object. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
variable {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x0 : (p f).Fiber (Over.mk kToS))

#check (AlgebraicGeometry.AlgebraicSpace.CohStack.predeformation f openImmersion kToS h_factor x0 :
  AlgebraicGeometry.AlgebraicSpace.CohStack.Predeformation.Obj f openImmersion kToS h_factor x0 ⥤
    ArtinianLocalAlgCat Λ k)
