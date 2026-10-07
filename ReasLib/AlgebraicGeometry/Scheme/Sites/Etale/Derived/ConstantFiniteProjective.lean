module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived.ChainMap
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived.Model
public import Mathlib.Topology.Connected.Basic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open DerivedCategory.TStructure

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [ConnectedSpace X]
variable {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  HasDerivedCategory (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  ((X.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]
variable [∀ U : X.Etale,
  (X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) U).Additive]
variable [∀ U : X.Etale,
  PreservesFiniteLimits (X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) U)]
variable [∀ U : X.Etale,
  PreservesFiniteColimits (X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) U)]

/-- A bounded constructible Tor-finite derived object on a connected scheme with
finite-type locally constant cohomology is represented on an étale cover by one
bounded complex of finite projective modules over the Noetherian coefficient ring. -/
theorem exists_finiteProjective_constant_model
    (K : Etale.Derived.ConstructibleTorFinite X Λ)
    (hKbounded :
      (t.bounded : ObjectProperty
        (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))) K.obj)
    (hKcohomology :
      DerivedCategory.cohomologyIn
        (CategoryTheory.Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ)
        K.obj) :
    ∃ M : CochainComplex (ModuleCat.{v} Λ) ℤ,
      M.IsBoundedFiniteProjective ∧
        ∃ T : X.smallEtaleTopology.Cover (⊤_ X.Etale),
          ∀ I : T.Arrow,
            Nonempty
              (DerivedRestriction.obj K.obj I.Y ≅
                DerivedRestriction.ofComplex
                  (DerivedRestriction.restrictConstantComplex M I.Y)) := sorry

end AlgebraicGeometry.Scheme
