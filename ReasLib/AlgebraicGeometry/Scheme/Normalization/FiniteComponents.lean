/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.CompactOpens
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Reduction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normalization and finite irreducible components

This file records decomposition, generic-point behavior, factorization, and lifting results for
relative and absolute normalizations under finite irreducible-component hypotheses.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative normalization of a quasi-compact and quasi-separated morphism from a normal
scheme with finitely many irreducible components on quasi-compact opens admits a pairwise disjoint
open cover by normal integral schemes. -/
theorem normalization_hasPairwiseDisjointOpenCoverByNormalIntegral_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    f.normalization.HasPairwiseDisjointOpenCoverByNormalIntegral := sorry

/-- The relative normalization of a quasi-compact and quasi-separated morphism from a normal
scheme with finitely many irreducible components on quasi-compact opens is normal. -/
theorem normalization_isNormal_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    f.normalization.isNormal := sorry

/-- The canonical map to the relative normalization of a quasi-compact and quasi-separated
morphism from a normal scheme with finitely many irreducible components on quasi-compact opens
bijects the generic points of its source and target. -/
theorem bijOn_genericPoints_toNormalization_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    Set.BijOn f.toNormalization (genericPoints Y) (genericPoints f.normalization) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

namespace Normalization

/-- The normalization of a scheme with finitely many irreducible components on quasi-compact
opens admits a pairwise disjoint open cover by normal integral schemes. -/
@[stacks 035Q]
theorem cover
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.normalization.HasPairwiseDisjointOpenCoverByNormalIntegral := sorry

/-- The normalization morphism of a scheme with finitely many irreducible components on
quasi-compact opens bijects the generic points of its source and target. -/
@[stacks 035Q]
theorem bijOn_genericPoints
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Set.BijOn X.normalizationTo (genericPoints X.normalization) (genericPoints X) := sorry

/-- The normalization morphism of a scheme with finitely many irreducible components on
quasi-compact opens is surjective. -/
@[stacks 035Q]
theorem surjective
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Surjective X.normalizationTo := sorry

/-- The normalization morphism of a reduced scheme with finitely many irreducible components is
birational. -/
theorem isBirational_of_isReduced_finiteComponents
    (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)] :
    IsBirational X.normalizationTo := sorry

attribute [instance] isBirational_of_isReduced_finiteComponents

/-- An integral morphism that is birational on quasi-compact opens receives the normalization
morphism of its target. The intermediate scheme has finite irreducible components on quasi-compact
opens, and the resulting map identifies the source normalization with its normalization. The
finite-component conclusion is bound as an instance only inside the remaining conclusion so that
the intermediate normalization and its canonical morphism are available there. -/
@[stacks 035Q]
theorem exists_factorization
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {X' : Scheme.{u}} (α : X' ⟶ X) [IsIntegralHom α]
    (hα : α.IsBirationalOnCompactOpens) :
    ∃ hX' : HasFiniteIrreducibleComponentsOnCompactOpens X',
      -- Local instance justification (proof-local temporary data): the existentially returned finite-component proof is installed only to form the intermediate normalization in this dependent conclusion.
      letI : HasFiniteIrreducibleComponentsOnCompactOpens X' := hX'
      ∃ β : X.normalization ⟶ X',
        β ≫ α = X.normalizationTo ∧
          ∃ e : X.normalization ≅ X'.normalization,
            β = e.hom ≫ X'.normalizationTo := sorry

/-- A morphism from a normal scheme that maps every generic point to a generic point factors
uniquely through the normalization morphism of a scheme with finitely many irreducible components
on quasi-compact opens. -/
@[stacks 035Q]
theorem existsUnique_lift_of_isNormal
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {Z : Scheme.{u}} (g : Z ⟶ X) (hZ : Z.isNormal)
    (hcomponents : Set.MapsTo g (genericPoints Z) (genericPoints X)) :
    ∃! h : Z ⟶ X.normalization, h ≫ X.normalizationTo = g := sorry

end Normalization

end AlgebraicGeometry.Scheme
