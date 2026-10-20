/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import Mathlib.Topology.QuasiSeparated

/-!
# Dense schematic locus from a finite étale scheme cover

A finite étale surjective morphism from a scheme onto an algebraic space makes
its schematic locus dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite étale surjective morphism from a scheme makes the schematic locus of
the target algebraic space dense. -/
theorem dense_schematicLocus_of_finiteEtaleCover {S : Scheme.{u}}
    {X U : AlgebraicSpace S} [IsScheme U] (f : U ⟶ X) [IsFinite f] [Etale f]
    [Surjective f] :
    Dense (schematicLocus X).pointsSet :=
  sorry

/-- An algebraic space admitting a finite étale surjective morphism from a scheme
has a dense open subspace representable by a scheme. -/
theorem exists_dense_open_isScheme_of_finiteEtaleCover {S : Scheme.{u}}
    {X U : AlgebraicSpace S} [IsScheme U] (f : U ⟶ X) [IsFinite f] [Etale f]
    [Surjective f] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet :=
  ⟨schematicLocus X, instIsScheme_schematicLocus X,
    dense_schematicLocus_of_finiteEtaleCover f⟩

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- A finite étale surjective morphism from a quasi-separated scheme places every
codimension-zero point of the target in its schematic locus. -/
theorem codimZero_subset_schematicLocus_of_finiteEtale (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left] :
    (setOf fun x : Points X ↦ localRingDimAt x = 0) ⊆ (schematicLocus X).pointsSet :=
  sorry

/-- An algebraic space admitting a finite étale surjective morphism from a
quasi-separated scheme has a dense open scheme subspace containing every
codimension-zero point. -/
theorem exists_dense_open_isScheme_of_finiteEtale (f : ofOver U ⟶ X)
    (hf_finite : (MorphismProperty.over (@AlgebraicGeometry.IsFinite)).presheaf f)
    (hf_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (hf_surj : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f)
    [QuasiSeparatedSpace U.left] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet ∧
      ∀ x : Points X, localRingDimAt x = 0 → x ∈ X'.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
