/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Noetherian
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Intrinsic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NormalizationDegree
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.Basic

/-!
# Normalization degree of a dualizing complex on an algebraic space

The integer function on `|X|` attached to a dualizing complex is the unique function whose
value at each point is the residue-field coextension degree of the derived étale stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived (stalkDerived)
open CategoryTheory.Limits
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The derived étale stalk of `ω` at the chosen geometric point over `x`. -/
noncomputable def geometricStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ω : DerivedQCoh X) (x : Points X) :
    DerivedCategory (ModuleCat (etaleLocalRing X (geometricPointOver x))) :=
  stalkDerived (geometricPointOver x) ((inclusion X).obj ω)

/-- A function records the normalization degrees of the derived étale stalks of `ω` when its
value at each point is the shift of the residue field obtained by derived coextension. -/
def IsGeometricStalkNormalizationDegreeFunction {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (ω : DerivedQCoh X) (δ : Points X → ℤ) : Prop :=
  ∀ x : Points X,
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap (etaleLocalRing X (geometricPointOver x))
            (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x))))).obj
          (geometricStalk ω x) ≅
        (shiftFunctor
            (DerivedCategory
              (ModuleCat.{u}
                (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))))
            (δ x)).obj
          (ModuleCat.single0
            (ModuleCat.of
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x))))))

/-- The residue-field characterization of a geometric-stalk normalization degree at a point. -/
theorem IsGeometricStalkNormalizationDegreeFunction.at {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {ω : DerivedQCoh X} {δ : Points X → ℤ}
    (hδ : IsGeometricStalkNormalizationDegreeFunction ω δ) (x : Points X) :
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap (etaleLocalRing X (geometricPointOver x))
            (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x))))).obj
          (geometricStalk ω x) ≅
        (shiftFunctor
            (DerivedCategory
              (ModuleCat.{u}
                (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))))
            (δ x)).obj
          (ModuleCat.single0
            (ModuleCat.of
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))
              (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))))) :=
  hδ x

/-- The normalization degree at a point is the negative infimum of the nonzero cohomology
degrees of the canonical residue-field derived coextension of the geometric stalk. -/
noncomputable def normalizationDegree {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : IsDualizingComplex ω) : Points X → ℤ :=
  fun x ↦ -sInf (setOf (fun i : ℤ ↦ ¬ IsZero
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))) i).obj
        ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap (etaleLocalRing X (geometricPointOver x))
            (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x))))).obj
          (geometricStalk ω x)))))

/-- The canonical normalization-degree function has the defining stalkwise property. -/
theorem normalizationDegree_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : IsDualizingComplex ω) :
    IsGeometricStalkNormalizationDegreeFunction ω (normalizationDegree hω) :=
  sorry

/-- Any geometric-stalk normalization-degree function of a fixed dualizing complex is the
canonical one. -/
theorem normalizationDegree_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : IsDualizingComplex ω) {δ : Points X → ℤ}
    (hδ : IsGeometricStalkNormalizationDegreeFunction ω δ) :
    δ = normalizationDegree hω :=
  sorry

/-- Shifting the derived étale stalk at the chosen geometric point over `x` by the negative
canonical normalization degree gives a normalized dualizing complex over the étale local
ring. -/
theorem normalizationDegree_stalkShift_isNormalized {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : IsDualizingComplex ω)
    (x : Points X) :
    DerivedCategory.IsNormalizedDualizing
      (hNoetherian := etaleLocalRing.instIsNoetherianRing (geometricPointOver x))
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} (etaleLocalRing X (geometricPointOver x))))
          (-(normalizationDegree hω x))).obj
        (geometricStalk ω x)) :=
  sorry

/-- If `xbar` lies over `x`, shifting the derived étale stalk at `xbar` by
`-(normalizationDegree hω x)` gives a normalized dualizing complex over
`etaleLocalRing X xbar`. -/
theorem normalizationDegree_stalkShift_isNormalized_of_liesOver {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {ω : DerivedQCoh X}
    (hω : IsDualizingComplex ω)
    {x : Points X} {xbar : GeometricPoint X} (hx : xbar.image = x) :
    DerivedCategory.IsNormalizedDualizing
      (hNoetherian := etaleLocalRing.instIsNoetherianRing xbar)
      ((shiftFunctor (DerivedCategory (ModuleCat.{u} (etaleLocalRing X xbar)))
          (-(normalizationDegree hω x))).obj
        (stalkDerived xbar ((inclusion X).obj ω))) :=
  sorry

/-- Along an étale scheme chart, the algebraic-space normalization degree pulls back to the
scheme-level normalization degree of a Zariski dualizing complex whose `ε*` recovers the
chart restriction. -/
theorem normalizationDegree_comp_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] {ω : DerivedQCoh X} (hω : IsDualizingComplex ω) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (ωU : Scheme.DerivedQCoh U.left) (hωU : Scheme.IsDualizingComplex ωU.obj)
    (hiso : IsIsomorphic
      ((toEtaleDerived U).obj ((ModuleDerived.pullback φ).obj ((inclusion X).obj ω)))
      ((SmallEtale.inclusion U.left).obj ((epsilonStar U.left).obj ωU))) :
    normalizationDegree hω ∘ Points.mapOfOver φ =
      Scheme.IsDualizingComplex.normalizationDegree hωU :=
  sorry

/-- The canonical normalization-degree function of a dualizing complex on a locally Noetherian
quasi-separated algebraic space is a dimension function. -/
@[instance]
theorem normalizationDegree_isDimensionFunction {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsQuasiSeparated X] {ω : DerivedQCoh X}
    (hω : IsDualizingComplex ω) :
    IsDimensionFunction (normalizationDegree hω) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
