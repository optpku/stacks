/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct

@[expose] public section

/-!
# The derived Künneth morphism for schemes

This module constructs the canonical map from the tensor product of two derived direct images
to the derived direct image of the external derived tensor product on a scheme fiber product.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.Hom
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
  (Limits.pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends
  (Limits.pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization
  (Limits.pullback a b).toRingedSpace]

variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom a.toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom b.toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom
    ((Limits.pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom))]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom
    ((Limits.pullback.snd a b).toLRSHom.toShHom ≫ b.toLRSHom.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.fst a b).toLRSHom.toShHom a.toLRSHom.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.snd a b).toLRSHom.toShHom b.toLRSHom.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b ≫ a).toLRSHom.toShHom).OplaxMonoidal]

/-- The derived external tensor product `L(p)^* K ⊗ L(q)^* M` on `X ×ₛ Y`. -/
noncomputable abbrev externalTensorProduct
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (M : RingedSpace.ModuleDerived Y.toRingedSpace) :
    RingedSpace.ModuleDerived (Limits.pullback a b).toRingedSpace :=
  (L((Limits.pullback.fst a b).toLRSHom.toShHom)^*).obj K ⊗
    (L((Limits.pullback.snd a b).toLRSHom.toShHom)^*).obj M

/-- The derived external tensor product is the tensor of the two canonical derived pullbacks. -/
theorem externalTensorProduct_def
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (M : RingedSpace.ModuleDerived Y.toRingedSpace) :
    externalTensorProduct a b K M =
      (L((Limits.pullback.fst a b).toLRSHom.toShHom)^*).obj K ⊗
        (L((Limits.pullback.snd a b).toLRSHom.toShHom)^*).obj M := sorry

/-- The adjunction-unit and pushforward-composition map from `R(a)_* K` to
`R(p ≫ a)_* L(p)^* K`. -/
noncomputable def leftLeg (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (R(a.toLRSHom.toShHom)_*).obj K ⟶
      (R((Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)_*).obj
        ((L((Limits.pullback.fst a b).toLRSHom.toShHom)^*).obj K) :=
  (R(a.toLRSHom.toShHom)_*).map
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
        (Limits.pullback.fst a b).toLRSHom.toShHom).unit.app K) ≫
    (RingedSpace.moduleDerivedPushforward.Composition.iso
      (Limits.pullback.fst a b).toLRSHom.toShHom a.toLRSHom.toShHom
      inferInstance).hom.app _

/-- The adjunction-unit and pushforward-composition map from `R(b)_* M` to
`R(p ≫ a)_* L(q)^* M`, transported across the pullback square. -/
noncomputable def rightLeg (M : RingedSpace.ModuleDerived Y.toRingedSpace) :
    (R(b.toLRSHom.toShHom)_*).obj M ⟶
      (R((Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)_*).obj
        ((L((Limits.pullback.snd a b).toLRSHom.toShHom)^*).obj M) :=
  (R(b.toLRSHom.toShHom)_*).map
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction
        (Limits.pullback.snd a b).toLRSHom.toShHom).unit.app M) ≫
    (RingedSpace.moduleDerivedPushforward.Composition.iso
      (Limits.pullback.snd a b).toLRSHom.toShHom b.toLRSHom.toShHom
      inferInstance).hom.app _ ≫
    eqToHom (congrArg
      (fun g : Limits.pullback a b ⟶ S ↦
        (R(g.toLRSHom.toShHom)_*).obj
          ((L((Limits.pullback.snd a b).toLRSHom.toShHom)^*).obj M))
      (Limits.pullback.condition :
        Limits.pullback.fst a b ≫ a = Limits.pullback.snd a b ≫ b)).symm

/-- The canonical derived Künneth morphism over the scheme fiber product. -/
noncomputable def map
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (M : RingedSpace.ModuleDerived Y.toRingedSpace) :
    (R(a.toLRSHom.toShHom)_*).obj K ⊗ (R(b.toLRSHom.toShHom)_*).obj M ⟶
      (R((Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)_*).obj
        (externalTensorProduct a b K M) :=
  (leftLeg a b K ⊗ₘ rightLeg a b M) ≫
    (RingedSpace.modulePullbackDerivedPushforwardAdjunction
      (Limits.pullback.fst a b ≫ a).toLRSHom.toShHom).relativeDerivedCupProduct
      (curriedTensor (RingedSpace.ModuleDerived S.toRingedSpace))
      (curriedTensor (RingedSpace.ModuleDerived (Limits.pullback a b).toRingedSpace))
      (Functor.OplaxMonoidal.δ
        (L((Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)^*))
      ((L((Limits.pullback.fst a b).toLRSHom.toShHom)^*).obj K)
      ((L((Limits.pullback.snd a b).toLRSHom.toShHom)^*).obj M)

/-- The Künneth morphism is the tensor of its two unit/composition legs followed by the
relative derived cup product. -/
theorem map_eq
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (M : RingedSpace.ModuleDerived Y.toRingedSpace) :
    map a b K M =
      (leftLeg a b K ⊗ₘ rightLeg a b M) ≫
        (RingedSpace.modulePullbackDerivedPushforwardAdjunction
          (Limits.pullback.fst a b ≫ a).toLRSHom.toShHom).relativeDerivedCupProduct
          (curriedTensor (RingedSpace.ModuleDerived S.toRingedSpace))
          (curriedTensor (RingedSpace.ModuleDerived (Limits.pullback a b).toRingedSpace))
          (Functor.OplaxMonoidal.δ
            (L((Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)^*))
          ((L((Limits.pullback.fst a b).toLRSHom.toShHom)^*).obj K)
          ((L((Limits.pullback.snd a b).toLRSHom.toShHom)^*).obj M) := sorry

/-- The derived Künneth morphism is natural in both derived module arguments. -/
theorem map_naturality
    {K K' : RingedSpace.ModuleDerived X.toRingedSpace}
    {M M' : RingedSpace.ModuleDerived Y.toRingedSpace}
    (k : K ⟶ K') (m : M ⟶ M') :
    ((R(a.toLRSHom.toShHom)_*).map k ⊗ₘ (R(b.toLRSHom.toShHom)_*).map m) ≫
        map a b K' M' =
      map a b K M ≫
        (R((Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)_*).map
          ((L((Limits.pullback.fst a b).toLRSHom.toShHom)^*).map k ⊗ₘ
            (L((Limits.pullback.snd a b).toLRSHom.toShHom)^*).map m) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

end
