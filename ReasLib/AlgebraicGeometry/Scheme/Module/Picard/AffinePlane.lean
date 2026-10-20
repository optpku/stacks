/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation

/-!
# Invertible sheaves on the affine plane
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open CategoryTheory.MonoidalCategory
open MvPolynomial
open Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Every invertible sheaf on two-dimensional affine space over a field is trivial. -/
theorem affineSpaceTwo_invertible_isTrivial (k : Type u) [Field k]
    (L : (AffineSpaceOverField k 2).Modules) [IsFiniteLocallyFreeOfRank 1 L] :
    Nonempty (L ≅ 𝟙_ (AffineSpaceOverField k 2).Modules) :=
  sorry

/-- Every invertible sheaf on any open subscheme of two-dimensional affine space over a field
is trivial. -/
theorem affineSpaceTwo_opens_invertible_isTrivial (k : Type u) [Field k]
    (U : (AffineSpaceOverField k 2).Opens) (L : U.toScheme.Modules)
    [IsFiniteLocallyFreeOfRank 1 L] :
    Nonempty (L ≅ 𝟙_ U.toScheme.Modules) :=
  sorry

/-- Every invertible sheaf on an open subscheme of two-dimensional affine space over a field
extends to an invertible sheaf on the whole affine plane. -/
theorem affineSpaceTwo_opens_exists_invertible_extension (k : Type u) [Field k]
    (U : (AffineSpaceOverField k 2).Opens) (L : U.toScheme.Modules)
    [IsFiniteLocallyFreeOfRank 1 L] :
    ∃ M : (AffineSpaceOverField k 2).Modules,
      IsFiniteLocallyFreeOfRank 1 M ∧ Nonempty (M.restrict U.ι ≅ L) :=
  sorry

/-- Two-dimensional affine space over `k` is isomorphic to `Spec (k[x, y])`. -/
def affineSpaceTwo_specIso (k : Type u) [Field k] :
    AffineSpaceOverField k 2 ≅ Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of k) ≪≫
    (Scheme.Spec.mapIso
        (renameEquiv k (Equiv.ulift.{u} : ULift.{u} (Fin 2) ≃ Fin 2)).toRingEquiv.toCommRingCatIso.op).symm

end AlgebraicGeometry
