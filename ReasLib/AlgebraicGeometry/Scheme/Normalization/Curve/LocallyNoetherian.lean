/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PointsOver
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Basic

@[expose] public section

/-!
# Normalization of locally Noetherian curves

The declarations here are curve-level consequences of the normalization
construction.  Generic normalization objects and stalk constructions remain
in their own smaller leaves.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Curve

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A one-dimensional locally Noetherian scheme has integral normalization morphism. -/
theorem isIntegralTo (hdim : topologicalKrullDim X = 1) :
    IsIntegralHom X.normalizationTo := sorry

/-- A one-dimensional locally Noetherian scheme has surjective normalization morphism. -/
theorem surjectiveTo (hdim : topologicalKrullDim X = 1) :
    Surjective X.normalizationTo := sorry

/-- Normalization induces a bijection on irreducible components of a locally Noetherian curve. -/
theorem normalizationTo_bijOn_irreducibleComponents
    (hdim : topologicalKrullDim X = 1) :
    Set.BijOn (fun Z : Set X.normalization ↦ X.normalizationTo '' Z)
      (irreducibleComponents X.normalization) (irreducibleComponents X) := sorry

/-- The normalization morphism of a locally Noetherian curve factors through its reduction. -/
theorem factorsThroughReduction (hdim : topologicalKrullDim X = 1) :
    ∃ νred : X.normalization ⟶ X.reduction,
      νred ≫ X.reductionι = X.normalizationTo := sorry

/-- A factor of the normalization through reduction is the normalization of the reduction. -/
theorem reductionFactorIsNormalization (hdim : topologicalKrullDim X = 1)
    {νred : X.normalization ⟶ X.reduction}
    (hνred : νred ≫ X.reductionι = X.normalizationTo) :
    ∃ e : X.normalization ≅ X.reduction.normalization,
      νred = e.hom ≫ X.reduction.normalizationTo := sorry

/-- A factor of the normalization through reduction is birational. -/
theorem reductionFactorIsBirational (hdim : topologicalKrullDim X = 1)
    {νred : X.normalization ⟶ X.reduction}
    (hνred : νred ≫ X.reductionι = X.normalizationTo) :
    IsBirational νred := sorry

/-- At a closed point of a locally Noetherian curve, the normalization pushforward stalk is the
integral closure in the total quotient ring of the reduced local ring. -/
theorem pushforwardStalkEquivReducedIntegralClosure (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ e : Stalk.pushforward X x ≃+* Stalk.reducedIntegralClosure X x,
      e.toRingHom.comp (Stalk.pushforwardMap X x) =
        algebraMap (X.presheaf.stalk x) (Stalk.reducedIntegralClosure X x) := sorry

/-- Every fiber of the normalization morphism of a locally Noetherian curve is finite. -/
theorem fiberFinite (hdim : topologicalKrullDim X = 1) (x : X) :
    (X.normalizationTo.pointsOver x).Finite := sorry

/-- Normalization induces finite residue-field extensions on a locally Noetherian curve. -/
theorem residueFieldFinite (hdim : topologicalKrullDim X = 1) (xν : X.normalization) :
    Module.Finite (X.residueField (X.normalizationTo xν))
      (X.normalization.residueField xν) := sorry

/-- A normalization point over `x` has residue field finite over `κ(x)` on a
locally Noetherian curve. -/
theorem residueFieldFiniteOver
    (hdim : topologicalKrullDim X = 1) (x : X)
    (xν : X.normalizationTo.pointsOver x) :
    Module.Finite (X.residueField x) (X.normalization.residueField xν) := sorry

/-- The normalization of a locally Noetherian curve has a pairwise-disjoint cover by integral,
normal, locally Noetherian open subschemes. -/
theorem existsDisjointOpenCover (hdim : topologicalKrullDim X = 1) :
    ∃ (ι : Type u) (U : ι → X.normalization.Opens),
      TopologicalSpace.IsOpenCover U ∧
        Pairwise (fun i j ↦ Disjoint (U i : Set X.normalization) (U j : Set X.normalization)) ∧
          ∀ i, IsIntegral (U i).toScheme ∧
            (U i).toScheme.isNormal ∧ IsLocallyNoetherian (U i).toScheme := sorry

/-- Every affine open of the normalization of a locally Noetherian curve is the spectrum of a
finite product of Dedekind domains. -/
theorem affineOpenIsoFiniteProductDedekind (hdim : topologicalKrullDim X = 1)
    (U : X.normalization.affineOpens) :
    ∃ (ι : Type u) (_hι : Finite ι) (R : ι → CommRingCat.{u})
      (e : (U : X.normalization.Opens).toScheme ≅ Spec (CommRingCat.of (Π i, R i))),
      ∀ i, IsDedekindDomain (R i) := sorry

end AlgebraicGeometry.Scheme.Normalization.Curve
