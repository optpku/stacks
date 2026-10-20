/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

section

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
  (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
  (h_source : eR.hom ≫ G.s.left =
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
  (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
  [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]

/- Lemma 39.23.6 (1): the map from the object scheme to the invariant spectrum is
surjective on underlying points. -/
@[stacks 03BL] #check
  (AlgebraicGeometry.GroupoidScheme.invariantSpectrumMap_surjective
    G tSharp eU eR h_source h_target :
    Function.Surjective (invariantSpectrumMap G tSharp eU).base)

variable (u₀ u₁ : G.U.left)

/- Lemma 39.23.6 (2): two underlying points have the same image in the invariant spectrum
exactly when they are joined by an arrow with the stated target and source. -/
@[stacks 03BL] #check
  (AlgebraicGeometry.GroupoidScheme.invariantSpectrumMap_apply_eq_iff
    G tSharp eU eR h_source h_target u₀ u₁ :
    (invariantSpectrumMap G tSharp eU).base u₀ =
        (invariantSpectrumMap G tSharp eU).base u₁ ↔
      ∃ r : G.R.left, G.t.left r = u₀ ∧ G.s.left r = u₁)

variable {k : Type u} [Field k] [IsAlgClosed k]

/- Lemma 39.23.6 (3): over an algebraically closed field, restriction from object-ring
points to invariant-ring points is surjective. -/
@[stacks 03BL] #check
  (AlgebraicGeometry.GroupoidScheme.invariantRingPoints_surjective
    G tSharp eU eR h_source h_target :
    Function.Surjective
      (fun a : A →+* k ↦ a.comp (tSharp.eqLocus (algebraMap A B)).subtype))

variable (a₀ a₁ : A →+* k)

/- Lemma 39.23.6 (4): over an algebraically closed field, two object-ring points restrict
equally exactly when they are the target and source restrictions of an arrow-ring point. -/
@[stacks 03BL] #check
  (AlgebraicGeometry.GroupoidScheme.invariantRingPoints_eq_iff
    G tSharp eU eR h_source h_target a₀ a₁ :
    a₀.comp (tSharp.eqLocus (algebraMap A B)).subtype =
        a₁.comp (tSharp.eqLocus (algebraMap A B)).subtype ↔
      ∃ b : B →+* k, b.comp tSharp = a₀ ∧ b.comp (algebraMap A B) = a₁)

end

end AlgebraicGeometry.GroupoidScheme
