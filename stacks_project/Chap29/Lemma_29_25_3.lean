/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Cover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u v w

/- Lemma 29.25.3 (1): a scheme morphism is flat exactly when every compatible pair of affine
opens induces a flat map from the target section ring to the source section ring. -/
@[stacks 01U5] #check
  (AlgebraicGeometry.Scheme.Hom.flat_iff_affineOpen_appLE_flat :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Flat f ↔
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
          ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
            (CommRingCat.Hom.hom (f.appLE V U e)).Flat)

/- Compatible open covers detect flatness of a scheme morphism. -/
#check
  (AlgebraicGeometry.Scheme.Hom.flat_iff_hasFlatOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Flat f ↔ Nonempty (AlgebraicGeometry.Scheme.Hom.FlatOpenCover.{u, v, w} f))

/- Compatible affine open covers whose induced section-ring maps are flat detect flatness. -/
#check
  (AlgebraicGeometry.Scheme.Hom.flat_iff_hasFlatAffineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Flat f ↔ Nonempty (AlgebraicGeometry.Scheme.Hom.FlatAffineOpenCover.{u, v, w} f))

/- Restricting a flat morphism to arbitrary compatible source and target opens preserves
flatness. -/
#check
  (AlgebraicGeometry.IsZariskiLocalAtSource.resLE
      (P := @AlgebraicGeometry.Flat) :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {V : S.Opens} {U : X.Opens}
      (e : U ≤ f ⁻¹ᵁ V),
      Flat f → Flat (f.resLE V U e))
