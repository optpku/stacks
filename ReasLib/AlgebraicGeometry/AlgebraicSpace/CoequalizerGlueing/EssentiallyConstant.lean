/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.Factorization
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Presentation

/-!
# Essential constancy of coequalizer glueing systems
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

variable {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}

/-- For a proper morphism that is an isomorphism away from a closed subspace of
a quasi-compact locally Noetherian algebraic space, the infinitesimal-neighbourhood
coequalizer system is essentially constant with value the ambient space. -/
@[stacks 0AGL]
theorem cocone_isEssentiallyConstant
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsQuasiCompact X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    (cocone f i h_iso).IsEssentiallyConstant :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
