/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantBaseChange

/-!
# Invariant base change compatibility import

This source-facing compatibility module reexports the reusable invariant-base-change core.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

#check (AlgebraicGeometry.GroupoidScheme.invariantBaseChange :
  {S : Scheme.{u}} → (G : GroupoidScheme S) →
    {A B C' : Type u} → [CommRing A] → [CommRing B] → [CommRing C'] → [Algebra A B] →
    (target : A →+* B) → (eU : Spec (CommRingCat.of A) ≅ G.U.left) →
    (eR : Spec (CommRingCat.of B) ≅ G.R.left) →
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom) →
    (h_target : eR.hom ≫ G.t.left =
      Spec.map (CommRingCat.ofHom target) ≫ eU.hom) →
    (γ : target.eqLocus (algebraMap A B) →+* C') → GroupoidScheme S)

end AlgebraicGeometry.GroupoidScheme
