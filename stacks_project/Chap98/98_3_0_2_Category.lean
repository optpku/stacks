/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Category

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x0 : X.p.Fiber (Over.mk kToS))

/- The category of residue lifts and its projection to Artinian local algebras. -/
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion kToS h_factor X x0 :
  Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.forget openImmersion kToS h_factor X x0 :
  Obj openImmersion kToS h_factor X x0 ⥤ ArtinianLocalAlgCat Λ k)
