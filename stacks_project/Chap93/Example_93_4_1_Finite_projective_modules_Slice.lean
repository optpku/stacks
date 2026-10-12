/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.Deformation

universe u

open CategoryTheory

#check
  (ArtinianLocalAlgCat.FiniteProjective.deformation :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] (V : Type u) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V],
      CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
        (ArtinianLocalAlgCat Λ k))
