/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.IntermediateField.Adjoin.Simple

/-!
# Geometric irreducibility in a simple-adjoin tower

The neutral owner `IntermediateField.Adjoin.Simple` supplies the canonical map
`M⟮x⟯ → L⟮x⟯`. This leaf records only the geometric-irreducibility consequence of
transcendence.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

namespace AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.AdjoinSimple

variable {M L K : Type u}
variable [Field M] [Field L] [Field K]
variable [Algebra M L] [Algebra L K] [Algebra M K] [IsScalarTower M L K]

/-- The transcendental tower criterion for the canonical simple-adjoin map. -/
@[stacks 0G32]
theorem of_transcendental
    (hML : GeometricallyIrreducible (Spec.map (ofHom (algebraMap M L))))
    (x : K) (hx : Transcendental L x) :
    GeometricallyIrreducible (Spec.map (ofHom
      (IntermediateField.Adjoin.Simple.map (M := M) (L := L) (K := K) x))) := sorry

end AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.AdjoinSimple
