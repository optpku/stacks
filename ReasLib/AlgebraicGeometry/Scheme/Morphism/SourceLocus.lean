/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard

/-!
# Source loci of scheme-morphism properties

This module defines the largest candidate open in the source of a scheme
morphism on which a given morphism property holds, together with its locality
and standard-topology transport interfaces.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace CategoryTheory.MorphismProperty

variable (P : MorphismProperty Scheme.{u}) {X Y X' : Scheme.{u}}

/-- The supremum of the source opens on which `f` has property `P`. -/
def sourceLocus (f : X ⟶ Y) : X.Opens :=
  sSup {U : X.Opens | P (U.ι ≫ f)}

/-- A point belongs to `P.sourceLocus f` exactly when it belongs to some source
open on which the restriction of `f` has property `P`. -/
theorem mem_sourceLocus (f : X ⟶ Y) (x : X) :
    x ∈ P.sourceLocus f ↔ ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f) := sorry

/-- Every source open on which the restriction of `f` has property `P` is
contained in `P.sourceLocus f`. -/
theorem sourceLocus_maximal (f : X ⟶ Y) (U : X.Opens)
    (hU : P (U.ι ≫ f)) : U ≤ P.sourceLocus f := sorry

/-- For a Zariski-local source property, `P.sourceLocus f` is the greatest
source open on which the restriction of `f` has property `P`. -/
theorem sourceLocus_isGreatest [IsZariskiLocalAtSource P] (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (P.sourceLocus f) := sorry

/-- For a Zariski-local source property, the source locus is all of the source
exactly when the original morphism has the property. -/
theorem sourceLocus_eq_top_iff [IsZariskiLocalAtSource P] (f : X ⟶ Y) :
    P.sourceLocus f = ⊤ ↔ P f := sorry

/-- For a source property local in a non-Zariski standard topology,
`P.sourceLocus f` is the greatest source open on which `f` has property `P`. -/
theorem sourceLocus_isGreatest_nonZariski
    (tau : StandardTopology) (h_tau : tau ≠ .zariski)
    [P.IsLocalAtSource tau.precoverage] (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (P.sourceLocus f) := sorry

/-- The source locus of an fppf-local property commutes with preimage along a
flat, locally finitely presented morphism. -/
theorem sourceLocus_preimage_fppf
    [P.IsLocalAtSource Scheme.fppfPrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Flat g] [LocallyOfFinitePresentation g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := sorry

/-- The source locus of a syntomic-local property commutes with preimage along
a syntomic morphism. -/
theorem sourceLocus_preimage_syntomic
    [P.IsLocalAtSource Scheme.bigSyntomicPrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Syntomic g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := sorry

/-- The source locus of a smooth-local property commutes with preimage along a
smooth morphism. -/
theorem sourceLocus_preimage_smooth
    [P.IsLocalAtSource Scheme.bigSmoothPrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Smooth g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := sorry

/-- The source locus of an étale-local property commutes with preimage along an
étale morphism. -/
theorem sourceLocus_preimage_etale
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Etale g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := sorry

end CategoryTheory.MorphismProperty
