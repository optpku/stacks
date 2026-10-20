/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Bounds
import StacksCheckRecall

/-!
# Constructible cohomology under derived compact-support pushforward

Derived lower shriek preserves bounded-below torsion constructible complexes,
and constructible complexes over a torsion coefficient ring.
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

/- Theorem 63.14.5 (1): the bounded-below torsion case. -/
@[stacks 0GL0]
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.cohomologyIn_constructible_of_plusTorsionConstructible X P Λ K :
    ∀ (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n],
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj K))

/- Theorem 63.14.5 (2): the torsion coefficient ring case. -/
@[stacks 0GL0]
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.cohomologyIn_constructible_of_isTorsion X P Λ K :
    ∀ (hΛ : AddMonoid.IsTorsion Λ)
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K),
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj K))

/- Torsion cohomology in the bounded-below case. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.etaleDerivedIsTorsion_obj_of_plusTorsionConstructible X P Λ K :
    ∀ (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n],
    etaleDerivedIsTorsion ((etaleDerivedLowerShriek X P).obj K))

/- Preservation of the input lower bound supplies boundedness below. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.isGE X P K :
    etaleDerivedIsTorsion K → ∀ a : ℤ, DerivedCategory.IsGE K a →
      DerivedCategory.IsGE ((etaleDerivedLowerShriek X P).obj K) a)

end AlgebraicGeometry.Scheme.Etale

end
