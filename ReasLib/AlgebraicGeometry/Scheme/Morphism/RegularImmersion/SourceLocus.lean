/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Smooth

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Graph

/-!
# Koszul-regular source loci in smooth ambient schemes

This module compares the Koszul-regular source loci of two immersions into
schemes smooth over a common base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsKoszulRegularImmersion

/-- For two immersions of the same scheme into schemes smooth over a common base,
membership in the Koszul-regular source locus is independent of the smooth ambient scheme. -/
theorem mem_sourceLocus_iff_of_smooth_ambient
    {S U P P' : Scheme.{u}} (p : P ⟶ S) (p' : P' ⟶ S)
    (i : U ⟶ P) (i' : U ⟶ P') [Smooth p] [Smooth p']
    [IsImmersion i] [IsImmersion i'] (u : U) (h_over : i ≫ p = i' ≫ p') :
    u ∈ CategoryTheory.MorphismProperty.sourceLocus
      (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i ↔
      u ∈ CategoryTheory.MorphismProperty.sourceLocus
        (fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) i' := sorry

end AlgebraicGeometry.IsKoszulRegularImmersion
