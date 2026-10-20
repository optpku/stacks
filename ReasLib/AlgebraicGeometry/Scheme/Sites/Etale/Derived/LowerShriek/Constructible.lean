module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType
public import Mathlib.GroupTheory.Torsion

/-!
# Constructible cohomology under derived étale lower shriek

Derived lower shriek preserves constructible cohomology for bounded-below torsion
complexes, and for arbitrary complexes over a torsion coefficient ring.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y)
variable [IsSeparated X.hom] [Scheme.Hom.FinitePresentation X.hom]
variable [hXqc : CompactSpace X.left] [hXqs : QuasiSeparatedSpace X.left]

include hXqc hXqs
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
variable (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ X.left) (G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))

namespace etaleDerivedLowerShriek

/-- Derived lower shriek along a separated morphism of finite presentation between
quasi-compact quasi-separated schemes sends bounded-below complexes with torsion
constructible cohomology over a Noetherian ring to complexes with constructible
cohomology. -/
theorem cohomologyIn_constructible_of_plusTorsionConstructible
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj K) :=
  sorry

/-- Over a Noetherian torsion ring, derived lower shriek along a separated morphism
of finite presentation between quasi-compact quasi-separated schemes preserves
constructible cohomology of arbitrary complexes. -/
theorem cohomologyIn_constructible_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ)
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj K) :=
  sorry

/-- Derived lower shriek along a separated morphism of finite presentation between
quasi-compact quasi-separated schemes sends bounded-below complexes with torsion
constructible cohomology over a Noetherian ring to complexes with torsion cohomology. -/
theorem etaleDerivedIsTorsion_obj_of_plusTorsionConstructible
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    etaleDerivedIsTorsion ((etaleDerivedLowerShriek X P).obj K) :=
  sorry

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
