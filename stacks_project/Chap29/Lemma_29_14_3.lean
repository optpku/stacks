/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.14.3: if `f : X ⟶ S` is locally of type `P` and `P` is local, then the
map on sections induced by compatible affine opens `U ⊆ X` and `V ⊆ S` has property `P`. -/
@[stacks 01ST] #check
  (AlgebraicGeometry.LocallyOfType.appLE_of_isAffineOpen :
    ∀ (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
      {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.LocallyOfType P f → RingHom.PropertyIsLocal P →
        ∀ {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U →
          ∀ {V : S.Opens}, AlgebraicGeometry.IsAffineOpen V →
            ∀ e : U ≤ f ⁻¹ᵁ V,
              P (CommRingCat.Hom.hom (f.appLE V U e)))
