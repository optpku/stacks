/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization.Smooth

/-!
# Pair henselization as a morphism of deformation categories

The canonical based functor and its underlying-functor identities.
-/

public section

open CategoryTheory Functor RingPairCat
open scoped BasedFunctor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P] (J : Ideal P)
variable [henselianPairInclusion.IsRightAdjoint]

#check (FlatAlgebraCat.henselizationFunctor_comp_forget Λ k P J :
  FlatAlgebraCat.henselizationFunctor Λ k P J ⋙
      FlatAlgebraCat.deformationForget Λ k (henselizationRing (pairOfIdeal J) : Type u) =
    FlatAlgebraCat.deformationForget Λ k P)

#check (FlatAlgebraCat.henselizationBasedFunctor Λ k P J :
  BasedCategory.ofFunctor (FlatAlgebraCat.deformationForget Λ k P) ⥤ᵇ
    BasedCategory.ofFunctor
      (FlatAlgebraCat.deformationForget Λ k (henselizationRing (pairOfIdeal J) : Type u)))

#check (FlatAlgebraCat.henselizationBasedFunctor_toFunctor Λ k P J :
  (FlatAlgebraCat.henselizationBasedFunctor Λ k P J).toFunctor =
    FlatAlgebraCat.henselizationFunctor Λ k P J)

end
