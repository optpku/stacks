/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.FreeQuotient
import StacksCheckRecall

/-!
# Schematic locus of a finite free quotient

A point of a finite free quotient `Y = X/G` of algebraic spaces lies in the
schematic locus if and only if some affine open of `X` contains the
set-theoretic fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFreeQuotient

/- Lemma 72.10.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`
and let `G` be a finite group acting freely on `X`. Set `Y = X/G` as in
Properties of Spaces, Lemma 66.34.1. For `y ∈ |Y|` the following are
equivalent: `y` is in the schematic locus of `Y`, and there exists an affine
open `U ⊂ X` containing the preimage of `y`. -/
@[stacks 0B87] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFreeQuotient.mem_schematicLocus_iff_exists_affineOpen :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
    (ρ : G →* Aut X) (q : X ⟶ Y) [IsFree ρ] [IsFreeQuotient ρ q]
    (y : Points Y),
    y ∈ (schematicLocus Y).pointsSet ↔
      ∃ U : OpenSubspace X, IsAffine U.X ∧ Points.map q ⁻¹' {y} ⊆ U.pointsSet)

end AlgebraicGeometry.AlgebraicSpace.IsFreeQuotient
