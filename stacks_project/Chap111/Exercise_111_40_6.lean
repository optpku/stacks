module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.AffinePlane
public import ReasLib.AlgebraicGeometry.QuadricCone.Punctured
import StacksCheckRecall

/-!
# Invertible sheaves on the affine plane and the punctured quadratic cone
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open CategoryTheory.MonoidalCategory
open Scheme.Modules

universe u

/- Exercise 111.40.6 (1): every invertible sheaf on two-dimensional affine space
over a field is trivial. -/
@[stacks 02AL] #check (AlgebraicGeometry.affineSpaceTwo_invertible_isTrivial :
  ∀ (k : Type u) [Field k] (L : (AffineSpaceOverField k 2).Modules)
    [IsFiniteLocallyFreeOfRank 1 L],
    Nonempty (L ≅ 𝟙_ (AffineSpaceOverField k 2).Modules))

/- Exercise 111.40.6 (2): every invertible sheaf on any open subscheme of
two-dimensional affine space over a field is trivial. -/
@[stacks 02AL] #check (AlgebraicGeometry.affineSpaceTwo_opens_invertible_isTrivial :
  ∀ (k : Type u) [Field k] (U : (AffineSpaceOverField k 2).Opens)
    (L : U.toScheme.Modules) [IsFiniteLocallyFreeOfRank 1 L],
    Nonempty (L ≅ 𝟙_ U.toScheme.Modules))

-- Every invertible sheaf on an open subscheme extends to the affine plane.
#check (AlgebraicGeometry.affineSpaceTwo_opens_exists_invertible_extension :
  ∀ (k : Type u) [Field k] (U : (AffineSpaceOverField k 2).Opens)
    (L : U.toScheme.Modules) [IsFiniteLocallyFreeOfRank 1 L],
    ∃ M : (AffineSpaceOverField k 2).Modules,
      IsFiniteLocallyFreeOfRank 1 M ∧ Nonempty (M.restrict U.ι ≅ L))

-- The affine plane is the spectrum of the polynomial ring in two variables.
#check (AlgebraicGeometry.affineSpaceTwo_specIso :
  ∀ (k : Type u) [Field k],
    AffineSpaceOverField k 2 ≅ Spec (CommRingCat.of (MvPolynomial (Fin 2) k)))

/- Exercise 111.40.6 (3): the punctured affine quadratic cone over a field admits
a nontrivial invertible sheaf. -/
@[stacks 02AL] #check (AlgebraicGeometry.QuadricCone.exists_nontrivial_invertibleSheaf :
  ∀ (k : Type u) [Field k],
    ∃ L : (QuadricCone.puncturedOpen k).toScheme.Modules,
      IsFiniteLocallyFreeOfRank 1 L ∧
        ¬ Nonempty (L ≅ 𝟙_ (QuadricCone.puncturedOpen k).toScheme.Modules))
