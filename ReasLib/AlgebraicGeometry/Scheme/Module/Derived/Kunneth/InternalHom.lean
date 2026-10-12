/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom

/-!
# The derived Künneth morphism for internal Homs

This module constructs the canonical morphism from the tensor product of two derived direct
images of internal Homs to the derived direct image of the internal Hom between external tensor
products.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal.InternalHom
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
  (pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends
  (pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization
  (pullback a b).toRingedSpace]

variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom a.toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom b.toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (pullback.fst a b).toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (pullback.snd a b).toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom (pullback.fst a b ≫ a).toLRSHom.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom
    ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom))]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom
    ((pullback.snd a b).toLRSHom.toShHom ≫ b.toLRSHom.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (pullback.fst a b).toLRSHom.toShHom a.toLRSHom.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (pullback.snd a b).toLRSHom.toShHom b.toLRSHom.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (pullback.fst a b ≫ a).toLRSHom.toShHom).OplaxMonoidal]
variable [(RingedSpace.modulePullbackDerived
  (pullback.fst a b).toLRSHom.toShHom).Monoidal]
variable [(RingedSpace.modulePullbackDerived
  (pullback.snd a b).toLRSHom.toShHom).Monoidal]

variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived (pullback a b).toRingedSpace)]

/-- The canonical morphism from the tensor of two derived pushforwards of internal Homs to the
derived pushforward of the internal Hom between the corresponding external tensor products. -/
noncomputable def homMap
    (K K' : RingedSpace.ModuleDerived X.toRingedSpace)
    (M M' : RingedSpace.ModuleDerived Y.toRingedSpace) :
    (R(a.toLRSHom.toShHom)_*).obj ((ihom K).obj K') ⊗
        (R(b.toLRSHom.toShHom)_*).obj ((ihom M).obj M') ⟶
      (R((pullback.fst a b ≫ a).toLRSHom.toShHom)_*).obj
        ((ihom (externalTensorProduct a b K M)).obj
          (externalTensorProduct a b K' M')) :=
  map a b ((ihom K).obj K') ((ihom M).obj M') ≫
    (R((pullback.fst a b ≫ a).toLRSHom.toShHom)_*).map
      (((comparison
          (RingedSpace.modulePullbackDerived (pullback.fst a b).toLRSHom.toShHom) K K') ⊗ₘ
        (comparison
          (RingedSpace.modulePullbackDerived (pullback.snd a b).toLRSHom.toShHom) M M')) ≫
        tensorHomComparison
          ((L((pullback.fst a b).toLRSHom.toShHom)^*).obj K)
          ((L((pullback.fst a b).toLRSHom.toShHom)^*).obj K')
          ((L((pullback.snd a b).toLRSHom.toShHom)^*).obj M)
          ((L((pullback.snd a b).toLRSHom.toShHom)^*).obj M'))

/-- The internal-Hom Künneth morphism is the derived Künneth map followed by the pullback
internal-Hom comparisons and the tensor-of-internal-Homs comparison. -/
theorem homMap_eq
    (K K' : RingedSpace.ModuleDerived X.toRingedSpace)
    (M M' : RingedSpace.ModuleDerived Y.toRingedSpace) :
    homMap a b K K' M M' =
      map a b ((ihom K).obj K') ((ihom M).obj M') ≫
        (R((pullback.fst a b ≫ a).toLRSHom.toShHom)_*).map
          (((comparison
              (RingedSpace.modulePullbackDerived
                (pullback.fst a b).toLRSHom.toShHom) K K') ⊗ₘ
            (comparison
              (RingedSpace.modulePullbackDerived
                (pullback.snd a b).toLRSHom.toShHom) M M')) ≫
            tensorHomComparison
              ((L((pullback.fst a b).toLRSHom.toShHom)^*).obj K)
              ((L((pullback.fst a b).toLRSHom.toShHom)^*).obj K')
              ((L((pullback.snd a b).toLRSHom.toShHom)^*).obj M)
              ((L((pullback.snd a b).toLRSHom.toShHom)^*).obj M')) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

end
