/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.FiniteEtale
import StacksCheckRecall

/-!
# Dense schematic locus from a finite étale scheme cover

A finite étale surjective morphism from a scheme onto an algebraic space forces
the existence of a dense open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.10.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If there exists a finite, étale, surjective morphism `U ⟶ X` where `U` is a
scheme, then there exists a dense open subspace of `X` which is a scheme. -/
@[stacks 06NG] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isScheme_of_finiteEtaleCover :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} [IsScheme U] (f : U ⟶ X)
      [IsFinite f] [Etale f] [Surjective f],
      ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet)

/- A finite étale surjective morphism from a scheme makes the schematic locus of
`X` dense in `Points X`. -/
#check (AlgebraicGeometry.AlgebraicSpace.dense_schematicLocus_of_finiteEtaleCover :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} [IsScheme U] (f : U ⟶ X)
    [IsFinite f] [Etale f] [Surjective f], Dense (schematicLocus X).pointsSet)

end AlgebraicGeometry.AlgebraicSpace
