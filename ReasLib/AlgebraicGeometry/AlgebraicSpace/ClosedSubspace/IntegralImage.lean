module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Integral images of closed subspaces

The integral image is the reduced induced structure on the closure of the image
of the generic point, characterized by dominant factorization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- The generic point of the integral algebraic space `Z.X`, determined by the
irreducible closed subset of its identity closed subspace. -/
noncomputable abbrev integralGenericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [h : IsIntegral Z.X] : Points Z.X :=
  irreducibleSetEquivPoints.toEquiv (@irreducibleClosed S Z.X (id Z.X) h)

/-- `integralGenericPoint Z` is a generic point of `|Z.X|`. -/
theorem isGenericPoint_integralGenericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    IsGenericPoint (integralGenericPoint Z) (Set.univ : Set (Points Z.X)) :=
  sorry

/-- The integral closed subspace of `Y` obtained as the reduced induced structure
on the closure of the image of the generic point of `Z` along `f`. -/
noncomputable def integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y) :
    ClosedSubspace Y :=
  ofIrreducibleClosed
    (irreducibleSetEquivPoints.toEquiv.symm
      (Points.map (Z.ι ≫ f) (integralGenericPoint Z)))

/-- The integral image is an integral closed subspace of `Y` whose underlying
point-set is the closure of the image of the generic point of `Z`. -/
theorem integralImage_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y) :
    IsIntegral (Z.integralImage f).X ∧
      IsGenericPoint (Points.map (Z.ι ≫ f) (integralGenericPoint Z))
        (Z.integralImage f).pointsSet ∧
      (Z.integralImage f).pointsSet =
        closure {Points.map (Z.ι ≫ f) (integralGenericPoint Z)} :=
  sorry

/-- The underlying point-set of the integral image is the closure of the image
of the generic point of `Z`. -/
theorem pointsSet_integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y) :
    (Z.integralImage f).pointsSet =
      closure {Points.map (Z.ι ≫ f) (integralGenericPoint Z)} :=
  sorry

/-- The image of the generic point of `Z` is a generic point of the integral
image. -/
theorem isGenericPoint_integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y) :
    IsGenericPoint (Points.map (Z.ι ≫ f) (integralGenericPoint Z))
      (Z.integralImage f).pointsSet :=
  sorry

/-- There is a unique morphism `g : Z.X ⟶ (Z.integralImage f).X` over `Y`
factoring `Z.ι ≫ f` through the inclusion of the integral image. -/
theorem existsUnique_hom_integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y) :
    ∃! g : Z.X ⟶ (Z.integralImage f).X,
      g ≫ (Z.integralImage f).ι = Z.ι ≫ f :=
  sorry

/-- Any integral closed subspace of `Y` admitting a dominant factorization of
`Z.ι ≫ f` has a unique morphism over `Y` to the integral image. -/
theorem unique_integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y)
    (W : ClosedSubspace Y) [IsIntegral W.X]
    (h_factor : ∃ g : Z.X ⟶ W.X, g ≫ W.ι = Z.ι ≫ f ∧ Dominant g) :
    ∃! φ : W.X ⟶ (Z.integralImage f).X, φ ≫ (Z.integralImage f).ι = W.ι :=
  sorry

/-- Any morphism `g : Z.X ⟶ (Z.integralImage f).X` over `Y` is dominant. -/
theorem dominant_hom_integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y)
    {g : Z.X ⟶ (Z.integralImage f).X}
    (hg : g ≫ (Z.integralImage f).ι = Z.ι ≫ f) :
    Dominant g :=
  sorry

/-- If `f` is proper, then any dominant factorization of `Z.ι ≫ f` through an
integral closed subspace of `Y` is proper. -/
theorem proper_hom_integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g) :
    Proper g :=
  sorry

/-- If `f` is proper, then any dominant factorization of `Z.ι ≫ f` through an
integral closed subspace of `Y` is surjective. -/
theorem surjective_hom_integralImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g) :
    Surjective g :=
  sorry

/-- An integral closed subspace has an integral closed image under a morphism
with decent target, admitting a dominant factorization and a unique comparison
over the target from every integral closed subspace with such a factorization. -/
theorem existsUnique_integralImage {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent Y] (f : X ⟶ Y)
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    ∃ Z' : ClosedSubspace Y,
      IsIntegral Z'.X ∧
        (∃ g : Z.X ⟶ Z'.X, g ≫ Z'.ι = Z.ι ≫ f ∧ Dominant g) ∧
          ∀ (W : ClosedSubspace Y),
            IsIntegral W.X →
              (∃ g : Z.X ⟶ W.X, g ≫ W.ι = Z.ι ≫ f ∧ Dominant g) →
                ∃! φ : W.X ⟶ Z'.X, φ ≫ Z'.ι = W.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
