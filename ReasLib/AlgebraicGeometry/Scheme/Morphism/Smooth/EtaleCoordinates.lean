module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.AtPoint
public import ReasLib.AlgebraicGeometry.AffineSpace.CoordinateInclusion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Étale coordinates for smooth morphisms

A morphism smooth at a point admits étale coordinates on an affine neighborhood
over any prescribed affine neighborhood of its image.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism smooth at a point admits an affine neighborhood with an étale map
to a relative affine space over any affine neighborhood of the image point. -/
theorem SmoothAt.exists_etale_affineSpace
    {X Y : Scheme} {f : X ⟶ Y} {x : X} (hx : f.SmoothAt x)
    (V : Y.affineOpens) (hxV : f x ∈ (V : Y.Opens)) :
    ∃ d : ℕ, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens),
        ∃ π : ((U : X.Opens).toScheme) ⟶ AffineSpace (Fin d) ((V : Y.Opens).toScheme),
          Etale π ∧
            π ≫ (AffineSpace (Fin d) ((V : Y.Opens).toScheme) ↘ ((V : Y.Opens).toScheme)) =
                    f.resLE (V : Y.Opens) (U : X.Opens) e := sorry

end AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry

/-- A morphism smooth at a point admits affine source and target neighborhoods together
with an étale map to a relative affine space that commutes with the restricted morphism. -/
theorem AlgebraicGeometry.Scheme.Hom.SmoothAt.exists_etale_affineSpaceNeighborhood
    {X Y : Scheme} {f : X ⟶ Y} {x : X} (hx : f.SmoothAt x) :
    ∃ d : ℕ, ∃ V : Y.affineOpens, ∃ U : X.affineOpens,
      x ∈ (U : X.Opens) ∧
        ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens),
          ∃ π : (U : X.Opens).toScheme ⟶
              AffineSpace (Fin d) (V : Y.Opens).toScheme,
            Etale π ∧
              π ≫ (AffineSpace (Fin d) (V : Y.Opens).toScheme ↘
                (V : Y.Opens).toScheme) = f.resLE V U e := sorry

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed immersion between schemes smooth over a base is locally the pullback of a
standard affine coordinate inclusion along an étale morphism. -/
theorem exists_etaleCoordinates_of_closedImmersion {S : Scheme.{u}}
    (X Y : Over S) (i : Y ⟶ X) [Smooth X.hom] [Smooth Y.hom]
    [IsClosedImmersion i.left] (y : Y.left) :
    ∃ m n : ℕ, ∃ U : X.left.Opens,
      let V := i.left ⁻¹ᵁ U
      y ∈ V ∧
        ∃ π : Over.mk (U.ι ≫ X.hom) ⟶
            Over.mk (𝔸(ULift.{u} (Fin (m + n)); S) ↘ S),
          ∃ q : Over.mk (V.ι ≫ Y.hom) ⟶
              Over.mk (𝔸(ULift.{u} (Fin m); S) ↘ S),
            Etale π.left ∧
              IsPullback q.left (i.left.resLE U V le_rfl)
                (AffineSpace.standardInclusion m n S) π.left := sorry

end AlgebraicGeometry.Scheme.Hom
