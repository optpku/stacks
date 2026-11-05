/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Etale.ClosedPointFrobenius
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.OverField.LFunction
public import ReasLib.CategoryTheory.Monoidal.Flat
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Lemma_59_71_5
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Theorem_64_20_1_Finite_Coefficients_Det

/-!
# Local Euler factors of constructible flat étale sheaves

The geometric point over a closed point and its residue-field Galois action
come from `ReasLib.AlgebraicGeometry.Scheme.Etale.ClosedPointFrobenius`.
The local factor `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` is supplied by
`LinearMap.eulerFactor`, and its constructible-flat specialization by
`SchemeOverField.eulerFactorClosedStalk`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory PowerSeries.WithPiTopology

variable {k : Type u} [Field k] [Fintype k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]

section LibraryAPI

variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]

-- Closed-point Galois automorphisms fix the residue field, so they act on the
-- canonical geometric point over that closed point.
#check (geometricPointGaloisIsoClosed :
  ∀ (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1)),
    Over.mk (geometricPointOverClosedPoint X x).hom ≅
      Over.mk (geometricPointOverClosedPoint X x).hom)

#check (geometricPointOverClosedPoint_image :
  ∀ (X : SchemeOverField k) (x : closedPoints X.left),
    (geometricPointOverClosedPoint X x).image = x.1)

#check (geometricStalkClosed_eq :
  ∀ {X : SchemeOverField k}
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left),
    geometricStalkClosed F x = (geometricStalkFunctorClosed x).obj F)

#check (geometricFrobeniusClosedStalk_spec :
  ∀ {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (x : closedPoints X.left),
    geometricFrobeniusClosedStalk F x =
      ModuleCat.Hom.hom
        ((GrothendieckTopology.Point.Hom.sheafFiber
            ⟨geometricPointFiberMap
              (Ω := AlgebraicClosure (X.left.residueField x.1))
              (geometricPointOverClosedPoint X x).hom
              (geometricPointGaloisIsoClosed X x
                (arithmeticFrobeniusEquivClosed X x)⁻¹)⟩).app F))

#check (finite_geometricStalkClosed :
  ∀ {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (x : closedPoints X.left),
    Module.Finite Λ (geometricStalkClosed F x))

section FlatStalks

variable [∀ {Y : Scheme.{u}},
    (Y.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

#check (projective_geometricStalkClosed :
  ∀ {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [MonoidalCategory.IsFlat F] (x : closedPoints X.left),
    Module.Projective Λ (geometricStalkClosed F x))

#check (eulerFactorClosedStalk :
  ∀ (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [MonoidalCategory.IsFlat F] (x : closedPoints X.left),
    PowerSeries Λ)

end FlatStalks

end LibraryAPI

section EulerFactors

variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom]
variable (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))

#check (fun (x : closedPoints X.left)
    [Module.Finite Λ (geometricStalkClosed F x)]
    [Module.Projective Λ (geometricStalkClosed F x)] ↦
  (LinearMap.eulerFactor_def (geometricFrobeniusClosedStalk F x)
      (X.hom.residueDegree x.1) :
    LinearMap.eulerFactor (geometricFrobeniusClosedStalk F x)
        (X.hom.residueDegree x.1) =
      PowerSeries.invOfUnit
        (Polynomial.toPowerSeries
          (Polynomial.expand Λ (X.hom.residueDegree x.1)
            (LinearMap.charpolyRev (geometricFrobeniusClosedStalk F x)))) 1))

-- The factor depends only on the underlying closed point.
example (x y : closedPoints X.left) (hxy : x.1 = y.1)
    [Module.Finite Λ (geometricStalkClosed F x)]
    [Module.Projective Λ (geometricStalkClosed F x)]
    [Module.Finite Λ (geometricStalkClosed F y)]
    [Module.Projective Λ (geometricStalkClosed F y)] :
    LinearMap.eulerFactor (geometricFrobeniusClosedStalk F x)
        (X.hom.residueDegree x.1) =
      LinearMap.eulerFactor (geometricFrobeniusClosedStalk F y)
        (X.hom.residueDegree y.1) := by
  have h : x = y := Subtype.ext hxy
  subst y
  rfl

-- Over the discrete finite coefficient ring, the local factors are multipliable.
example [∀ x : closedPoints X.left, Module.Finite Λ (geometricStalkClosed F x)]
    [∀ x : closedPoints X.left, Module.Projective Λ (geometricStalkClosed F x)] :
    letI : TopologicalSpace Λ := ⊥
    Multipliable fun x : closedPoints X.left ↦
      LinearMap.eulerFactor (geometricFrobeniusClosedStalk F x)
        (X.hom.residueDegree x.1) := by
  sorry

end EulerFactors
