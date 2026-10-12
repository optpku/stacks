/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap72.«72_12_5_1_Galois»
public import stacks_project.Chap72.Lemma_72_12_6_Galois

/-!
# Galois descent of quasi-compact opens of algebraic spaces

A quasi-compact open of an algebraic space after a possibly infinite Galois
field extension descends to a finite intermediate extension, and is stabilized
by an open subgroup of the Galois group.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace FieldExtension.Galois.CompactOpen

/-- Lemma 72.12.6 (1): Let `k` be a field. Let `X` be an algebraic space over
`k`. Let `kbar` be a (possibly infinite) Galois extension of `k`. Let `V` be a
quasi-compact open subspace of the field-extension base change of `X` to
`kbar`. Then there exists a finite subextension `kbar / K' / k` and a
quasi-compact open subspace `V'` of the field-extension base change of `X` to
`K'` such that `V` is the preimage of `V'` along the canonical projection
`baseChange k kbar X ⟶ baseChange k K' X`. -/
@[stacks 0A15]
theorem exists_finiteSubextension_preimage_eq
    {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
    (X : AlgebraicSpace (Spec (of k)))
    (V : OpenSubspace (FieldExtension.baseChange k kbar X))
    [IsQuasiCompact V.X] :
    ∃ (K' : IntermediateField k kbar) (_ : FiniteDimensional k K')
      (V' : OpenSubspace (FieldExtension.baseChange k K' X))
      (_ : IsQuasiCompact V'.X),
      IsBaseChangeFromIntermediate K' V V' :=
  sorry

/-- Lemma 72.12.6 (2): Let `k` be a field. Let `X` be an algebraic space over
`k`. Let `kbar` be a (possibly infinite) Galois extension of `k`. Let `V` be a
quasi-compact open subspace of the field-extension base change of `X` to
`kbar`. Then there exists an open subgroup `H ⊆ Gal(kbar/k)` such that
`σ(V) = V` for all `σ ∈ H`. -/
@[stacks 0A15]
theorem exists_openSubgroup_stabilizing
    {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
    (X : AlgebraicSpace (Spec (of k)))
    (V : OpenSubspace (FieldExtension.baseChange k kbar X))
    [IsQuasiCompact V.X] :
    ∃ (H : OpenSubgroup Gal(kbar/k)),
      ∀ σ : H,
        Points.map (FieldExtension.Galois.map k kbar X σ.1) '' V.pointsSet =
          V.pointsSet :=
  sorry

end FieldExtension.Galois.CompactOpen
end AlgebraicGeometry.AlgebraicSpace
