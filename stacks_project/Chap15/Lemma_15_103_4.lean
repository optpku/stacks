/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.ProjectiveDimension.Surjective

/-!
# Lemma 15.103.4

@stack 0929
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.103.4 (0929): for a Noetherian local ring `R`, an ideal `I`, and a nonzero finite
`R ⧸ I`-module `E`, finite projective dimensions satisfy
`pd_R(E) = pd_R(R ⧸ I) + pd_(R ⧸ I)(E)`.  The reusable owner is phrased through the canonical
surjective local algebra map and restriction-of-scalars functor. -/

@[stacks 0929 "Lemma 15.103.4 (finite projective dimension)"]
#check fun {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) {E : Type u} [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.Finite (R ⧸ I) E] [Nontrivial E]
    (hR : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hE : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) ↦
  (ModuleCat.RestrictScalars.Surjective.projectiveDimension_ne_top
    (R := R) (S := R ⧸ I) (M := ModuleCat.of (R ⧸ I) E)
    Ideal.Quotient.mk_surjective hR hE :
      projectiveDimension
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
            (ModuleCat.of (R ⧸ I) E)) ≠ ⊤)

@[stacks 0929 "Lemma 15.103.4 (projective dimension additivity)"]
#check fun {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) {E : Type u} [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.Finite (R ⧸ I) E] [Nontrivial E]
    (hR : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hE : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) ↦
  (ModuleCat.RestrictScalars.Surjective.projectiveDimension_eq_add
    (R := R) (S := R ⧸ I) (M := ModuleCat.of (R ⧸ I) E)
    Ideal.Quotient.mk_surjective hR hE :
      projectiveDimension
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
            (ModuleCat.of (R ⧸ I) E)) =
        projectiveDimension (ModuleCat.of R (R ⧸ I)) +
          projectiveDimension (ModuleCat.of (R ⧸ I) E))
