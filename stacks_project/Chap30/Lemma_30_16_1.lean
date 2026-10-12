/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

/- Lemma 30.16.1 (1): the section ring of an ample invertible module on a proper scheme over a
Noetherian affine base is a finite-type algebra over the base ring. -/
@[stacks 0B5T] #check
  (@AlgebraicGeometry.Scheme.Modules.IsAmple.sectionRing_finiteType :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (L : X.Modules) [L.Invertible] [Scheme.Modules.IsAmple L],
      Algebra.FiniteType R (Scheme.Hom.sectionRingAlg f L))

/- Lemma 30.16.1 (2): a coherent module is an epimorphic image of a finite coproduct of
integral powers of an ample invertible module. -/
@[stacks 0B5T] #check
  (@AlgebraicGeometry.Scheme.Modules.IsAmple.exists_epi_from_tensorPowers :
    ∀ {X : Scheme.{u}} {L : X.Modules} [L.Invertible],
      Scheme.Modules.IsAmple L →
      ∀ (F : X.Modules) [F.IsCoherent],
        ∃ (r : ℕ) (d : Fin r → ℤ)
          (π : (∐ fun j : Fin r ↦ L ^⊗ d j) ⟶ F), Epi π)

/- Lemma 30.16.1 (3): cohomology of a coherent module is finite over a Noetherian affine base
when the structure morphism is proper. -/
@[stacks 0B5T] #check
  (@AlgebraicGeometry.Scheme.Hom.cohomologyFinite :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (F : X.Modules) [F.IsCoherent] (p : ℕ),
      Module.Finite R (Scheme.Hom.cohomology f F p))

/- Lemma 30.16.1 (4): positive-degree cohomology of a coherent module twisted by sufficiently
large powers of an ample invertible module vanishes. -/
@[stacks 0B5T] #check
  (@AlgebraicGeometry.Scheme.Modules.IsAmple.twistCohomology_eventually_isZero :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (L F : X.Modules) [L.Invertible] [Scheme.Modules.IsAmple L] [F.IsCoherent]
      (p : ℕ), 0 < p →
      ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
        IsZero (Scheme.Hom.cohomology f (F ⊗ L ^⊗ d) p))

/- Lemma 30.16.1 (5): every lower truncation of the canonically acted-on twisted global
sections of a coherent module is finite over the section ring. -/
@[stacks 0B5T] #check
  (@AlgebraicGeometry.Scheme.Modules.IsAmple.truncatedSections_finite :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (L F : X.Modules) [L.Invertible] [Scheme.Modules.IsAmple L] [F.IsCoherent]
      (k : ℤ),
      Module.Finite (RingedSpace.GradedSections.ring L)
        (RingedSpace.GradedSections.truncatedTwisted L F k))
