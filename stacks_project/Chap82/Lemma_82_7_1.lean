module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap82.Lemma_82_7_1_IntegralImage

/-!
# Image of an integral closed subspace along a morphism over a base

In the good setup, an integral closed subspace of `X` has a unique integral
image in `Y` along a morphism over `B`, and that image morphism is proper and
surjective when `f` is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- Lemma 82.7.1 (1): In Situation 82.2.1 let `X, Y / B` be good and let
`f : X ⟶ Y` be a morphism over `B`. If `Z ⊂ X` is an integral closed subspace,
then there exists a unique integral closed subspace `Z' ⊂ Y` such that there is
a commutative square `Z.ι ≫ f = g ≫ Z'.ι` with `g : Z.X ⟶ Z'.X` dominant.
Uniqueness is a unique morphism over `Y`. A witness is `Z.integralImage f`, the
reduced induced integral closed subspace of `Y` through the image of the
generic point of `Z`. -/
@[stacks 0EEG]
theorem existsUnique_integralImage {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDecent Y]
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    ∃ Z' : ClosedSubspace Y,
      IsIntegral Z'.X ∧
        (∃ g : Z.X ⟶ Z'.X, g ≫ Z'.ι = Z.ι ≫ f ∧ Dominant g) ∧
          ∀ (W : ClosedSubspace Y),
            IsIntegral W.X →
              (∃ g : Z.X ⟶ W.X, g ≫ W.ι = Z.ι ≫ f ∧ Dominant g) →
                ∃! φ : W.X ⟶ Z'.X, φ ≫ Z'.ι = W.ι :=
  sorry

/-- Lemma 82.7.1 (2): In Situation 82.2.1 let `X, Y / B` be good and let
`f : X ⟶ Y` be a morphism over `B`. If `Z ⊂ X` is an integral closed subspace
and `f` is proper, then any dominant `g : Z.X ⟶ Z'.X` making the
closed-immersion square with `f` commute is proper. -/
@[stacks 0EEG]
theorem existsUnique_integralImage_proper {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDecent Y] [Proper f]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g) :
    Proper g :=
  sorry

/-- Lemma 82.7.1 (3): In Situation 82.2.1 let `X, Y / B` be good and let
`f : X ⟶ Y` be a morphism over `B`. If `Z ⊂ X` is an integral closed subspace
and `f` is proper, then any dominant `g : Z.X ⟶ Z'.X` making the
closed-immersion square with `f` commute is surjective. -/
@[stacks 0EEG]
theorem existsUnique_integralImage_surjective {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) (pY : Y ⟶ B)
    [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IsDecent Y] [Proper f]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g) :
    Surjective g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
