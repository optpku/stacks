module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Frobenius.Derived

/-! # Compatibility for derived étale module Frobenius comparisons -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open Opposite ComplexShape
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- Inverse image of a small-étale sheaf of left `Λ`-modules along a morphism of
schemes. -/
abbrev etaleModuleSheafPullback (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
  Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)

end AlgebraicGeometry.Scheme.Hom

#check (AlgebraicGeometry.Scheme.Hom.etaleModuleSheafPullback_eq :
  ∀ (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P],
    etaleModuleSheafPullback Λ f =
      (smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)

section
variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [Ring Λ] [Finite Λ]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (X : SchemeOverField k)

#check (AlgebraicGeometry.SchemeOverField.geometricFrobeniusComparison X :
  ∀ (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))),
    (etaleModuleSheafPullback Λ (geometricFrobenius_ofFiniteField X)).mapDerivedCategory.obj K ⟶ K)

#check (AlgebraicGeometry.SchemeOverField.geometricFrobeniusRGamma X :
  ∀ (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))),
    geometricRGamma X K ⟶ geometricRGamma X K)

end
