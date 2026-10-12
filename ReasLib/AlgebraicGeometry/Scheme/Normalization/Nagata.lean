/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian

/-!
# Relative normalization over a Nagata scheme

This module records a finiteness criterion for the relative normalization of a scheme morphism.
-/

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative normalization of a quasi-compact, quasi-separated morphism into a Nagata
scheme is finite when the source is reduced, its quasi-compact opens have finitely many
irreducible components, and its generic-point residue-field extensions are finitely generated. -/
theorem isFinite_fromNormalization_of_nagata
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.Nagata S] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] [IsReduced X]
    (hfg :
      ∀ x : X, x ∈ genericPoints X →
        Algebra.FiniteType (S.residueField (f x)) (X.residueField x)) :
    IsFinite f.fromNormalization := sorry

/-- The relative normalization of a reduced finite-type scheme over a Nagata scheme is finite. -/
theorem isFinite_fromNormalization_of_nagata_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [FiniteType f] [Scheme.Nagata S] [IsReduced X] :
    IsFinite f.fromNormalization := sorry

/-- Finiteness of the relative normalization of a reduced finite-type scheme over a Nagata
scheme is available canonically. -/
instance instIsFiniteFromNormalizationOfNagataFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [FiniteType f] [Scheme.Nagata S] [IsReduced X] :
    IsFinite f.fromNormalization :=
  isFinite_fromNormalization_of_nagata_of_finiteType f

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- The normalization morphism of a Nagata scheme is finite. -/
theorem isFinite_normalizationTo_of_nagata (X : Scheme.{u}) [Nagata X] :
    IsFinite X.normalizationTo := sorry

/-- Finiteness of the normalization morphism of a Nagata scheme is available canonically. -/
instance instIsFiniteNormalizationToOfNagata (X : Scheme.{u}) [Nagata X] :
    IsFinite X.normalizationTo :=
  isFinite_normalizationTo_of_nagata X

end AlgebraicGeometry.Scheme
