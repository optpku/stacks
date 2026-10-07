module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.PicardGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation
public import stacks_project.Chap111.Exercise_111_40_6_PuncturedCone
import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertible sheaves on the affine plane and the punctured quadratic cone
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open CategoryTheory.MonoidalCategory
open MvPolynomial
open Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Exercise 111.40.6 (1): every invertible sheaf on two-dimensional affine space
`AffineSpaceOverField k 2` over a field `k` is trivial. -/
@[stacks 02AL]
theorem affineSpaceTwo_invertible_isTrivial (k : Type u) [Field k]
    (L : (AffineSpaceOverField k 2).Modules) [IsFiniteLocallyFreeOfRank 1 L] :
    Nonempty (L ≅ 𝟙_ (AffineSpaceOverField k 2).Modules) :=
  sorry

/-- Exercise 111.40.6 (2): every invertible sheaf on any open subscheme of two-dimensional
affine space over a field `k` is trivial. -/
@[stacks 02AL]
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

/-- Every invertible module over the polynomial ring in two variables over a field is free of
rank one. -/
theorem mvPolynomialTwo_invertible_linearEquiv (k : Type u) [Field k] (M : Type u)
    [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Invertible (MvPolynomial (Fin 2) k) M] :
    Nonempty (M ≃ₗ[MvPolynomial (Fin 2) k] MvPolynomial (Fin 2) k) :=
  sorry

/-- The Picard group of two-dimensional affine space over a field is trivial. -/
instance instSubsingletonPicardGroup_affineSpaceTwo (k : Type u) [Field k] :
    Subsingleton (AffineSpaceOverField k 2).PicardGroup :=
  sorry

/-- The Picard group of any open subscheme of two-dimensional affine space over a field is
trivial. -/
instance instSubsingletonPicardGroup_affineSpaceTwo_opens (k : Type u) [Field k]
    (U : (AffineSpaceOverField k 2).Opens) :
    Subsingleton U.toScheme.PicardGroup :=
  sorry

namespace QuadricCone

/-- Exercise 111.40.6 (3): the punctured affine quadratic cone over a field admits a nontrivial
invertible sheaf. -/
@[stacks 02AL]
theorem exists_nontrivial_invertibleSheaf (k : Type u) [Field k] :
    ∃ L : (puncturedOpen k).toScheme.Modules,
      IsFiniteLocallyFreeOfRank 1 L ∧
        ¬ Nonempty (L ≅ 𝟙_ (puncturedOpen k).toScheme.Modules) :=
  sorry

end QuadricCone

end AlgebraicGeometry
