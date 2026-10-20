/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.LFunction
public import stacks_project.Chap59.Definition_59_77_1

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y : Scheme.{u}},
    (Y.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

#check (AlgebraicGeometry.SchemeOverField.lFunction :
  ∀ (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom],
    Nat.Coprime (Nat.card Λ) p →
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) →
    Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F →
    [IsFlat F] → PowerSeries Λ)

variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    Abelian (Sheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasDerivedCategory (Sheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    ((Y.smallEtaleTopology.over U).W (A := ModuleCat.{u} Λ)).IsMonoidal]

#check (AlgebraicGeometry.SchemeOverField.lFunctionDerived :
  ∀ (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom],
    Nat.Coprime (Nat.card Λ) p →
    (K : Scheme.Etale.Derived.ConstructibleTorFinite X.left Λ) →
    (∀ x : closedPoints X.left,
      DerivedCategory.IsPerfect (geometricDerivedStalkClosed K.obj x)) →
    PowerSeries Λ)

end AlgebraicGeometry.SchemeOverField
