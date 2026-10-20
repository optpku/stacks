/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Unramified.Field
public import ReasLib.RingTheory.Unramified.TensorSquare
import ReasLib.RingTheory.Etale.Weakly.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Separable field extensions from a flat tensor square

This leaf owns the field-extension consequence of the tensor-square flatness criterion.  The
statement is phrased using the canonical map-level owner of tensor-square multiplication, so
consumers do not need to reconstruct the algebra structure induced by `lmul'`.

@stack 092P
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.IsSeparable

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Lemma 15.105.15, tag `092P`: flatness of the tensor-square multiplication map
`L ⊗[K] L → L` forces the field extension `L / K` to be algebraic and separable. -/
@[stacks 092P "flat tensor-square multiplication implies separability"]
theorem of_tensorSquareMul_flat
    (hflat : (Algebra.tensorSquareMultiplication K L).Flat) :
    Algebra.IsSeparable K L := by
  refine ⟨fun x ↦ ?_⟩
  let M : IntermediateField K L := IntermediateField.adjoin K {x}
  letI : Algebra M L := M.val.toAlgebra
  letI : IsScalarTower K M L := inferInstance
  have hML : (algebraMap M L).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMflat : (Algebra.tensorSquareMultiplication K M).Flat :=
    Algebra.TensorSquare.flat_of_faithfullyFlat hML hflat
  letI : Algebra.FormallyUnramified K M :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hMflat
  letI : Algebra.EssFiniteType K M := (IntermediateField.essFiniteType_iff).2 <|
    by simpa [M] using IntermediateField.fg_adjoin_finset ({x} : Finset L)
  have : Algebra.IsSeparable K M := Algebra.FormallyUnramified.isSeparable K M
  exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mp <|
    by simpa [M] using this

end Algebra.IsSeparable
