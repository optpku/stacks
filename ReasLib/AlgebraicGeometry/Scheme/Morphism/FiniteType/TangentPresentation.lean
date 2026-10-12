/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.NoetherNormalization

/-!
# Presentations controlled by tangent-space rank

This file provides local presentations of finite type scheme morphisms whose dimensions are
controlled by the rank of the relative tangent space at a point.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite type morphism admits, near a point and over an affine target neighborhood,
either an immersion into relative affine space of dimension one greater than the tangent-space
rank or a closed immersion into a scheme smooth of that rank. -/
theorem exists_affineOpen_tangentRankPresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens))
    (r : ℕ) (hr : r = Module.finrank (X.residueField x) (tangentSpaceAt f x)) :
    (∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        ∃ j : (U : X.Opens).toScheme ⟶
            AffineSpace (ULift.{u} (Fin (r + 1))) (V : S.Opens).toScheme,
          IsImmersion j ∧
            j ≫ (AffineSpace (ULift.{u} (Fin (r + 1))) (V : S.Opens).toScheme ↘
              (V : S.Opens).toScheme) =
              f.resLE (V : S.Opens) (U : X.Opens) e) ∨
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          ∃ D : Scheme.{u},
            ∃ g : D ⟶ (V : S.Opens).toScheme,
              SmoothOfRelativeDimension r g ∧
                ∃ j : (U : X.Opens).toScheme ⟶ D,
                  IsClosedImmersion j ∧
                    j ≫ g = f.resLE (V : S.Opens) (U : X.Opens) e := sorry

end AlgebraicGeometry.Scheme.Hom
