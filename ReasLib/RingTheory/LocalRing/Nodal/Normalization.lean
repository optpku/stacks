/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Nodal
public import ReasLib.RingTheory.LocalRing.Branches
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normalization.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

noncomputable section

open IsLocalRing

universe u v w

namespace IsLocalRing

/-- For a Nagata local `k`-algebra, the reduced quadratic nodal condition is equivalent to
separability of the residue field, reducedness, dimension one, normalization `δ`-invariant
one, and two geometric branches. -/
theorem nodalLocalAlgebra_iff_invariants
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    (Ash : Type w) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash] :
    let κ := ResidueField A
    let V := CotangentSpace A
    let hasQuadraticRelation :=
      ∃ (e : Module.Basis (Fin 2) κ V) (a b c : κ),
        4 * a * c - b ^ 2 ≠ 0 ∧
          idealConormalAlgebraQuotient (maximalIdeal A)
              (a • SymmetricAlgebra.ι κ V (e 0) ^ 2 +
                b • (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) +
                c • SymmetricAlgebra.ι κ V (e 1) ^ 2) = 0
    let nodalCondition :=
      Algebra.IsSeparableOver k κ ∧ IsReduced A ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let invariantCondition :=
      Algebra.IsSeparableOver k κ ∧ IsReduced A ∧ ringKrullDim A = 1 ∧
        Normalization.deltaInvariant A = 1 ∧ geometricBranchNumber A Ash = 2
    nodalCondition ↔ invariantCondition := sorry

end IsLocalRing

namespace Normalization

/-- The normalization of a reduced one-dimensional Nagata local algebra with separable
residue field, `δ`-invariant one, and two geometric branches has one or two maximal ideals. -/
theorem maximalSpectrum_card_of_nodal
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    (Ash : Type w) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra.IsSeparableOver k (ResidueField A)] [IsReduced A]
    (h_dimension : ringKrullDim A = 1)
    (h_delta : Normalization.deltaInvariant A = 1)
    (h_branches : geometricBranchNumber A Ash = 2) :
    ENat.card (MaximalSpectrum (Normalization.normalizationRing A)) = 1 ∨
      ENat.card (MaximalSpectrum (Normalization.normalizationRing A)) = 2 := sorry

/-- Every residue field of the normalization of a reduced one-dimensional Nagata local
`k`-algebra with separable residue field, `δ`-invariant one, and two geometric branches is
separable over `k` through the canonical composite algebra map. -/
theorem residueField_isSeparableOver_of_nodal
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    (Ash : Type w) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra.IsSeparableOver k (ResidueField A)] [IsReduced A]
    (h_dimension : ringKrullDim A = 1)
    (h_delta : Normalization.deltaInvariant A = 1)
    (h_branches : geometricBranchNumber A Ash = 2)
    (m : MaximalSpectrum (Normalization.normalizationRing A)) :
    Algebra.IsSeparableOver k m.ResidueField := sorry

end Normalization
