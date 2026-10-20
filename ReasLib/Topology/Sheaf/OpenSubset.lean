module

public import ReasLib.Topology.Opens.Inclusion
public import ReasLib.Topology.Sheaf.Pullback

/-!
# Restriction of sheaves to open subspaces

This module owns the coefficient-independent restriction of a sheaf to an open subspace, together
with the canonical comparison maps for nested open inclusions. Coefficient-specific modules may
add notation or structure on top of this API, but should reuse these maps directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open TopologicalSpace.Opens
open TopCat.Opens.Subspace

noncomputable section

universe w v u

namespace TopCat.Sheaf.OpenSubset

variable {A : Type u} [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {X : TopCat.{w}}

/-- The restriction of an `A`-valued sheaf to an open subset, regarded as a sheaf on the
corresponding open subspace. -/
abbrev restrict (𝓕 : TopCat.Sheaf A X) (U : Opens X) :
    TopCat.Sheaf A (space U) :=
  (TopCat.Sheaf.pullback A (inclusion U)).obj 𝓕

namespace Restriction

/-- For an open inclusion, restriction along the counit of the adjunction on opens agrees with
the sheaf pullback-pushforward unit followed by the open-embedding pullback comparison. -/
theorem openEmbeddingCounitEq
    (U : Opens X) (𝓕 : TopCat.Sheaf A X) :
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) 𝓕.obj =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A (inclusion U)).unit.app 𝓕).hom ≫
        (Opens.map (inclusion U)).op.whiskerLeft
          (((U.isOpenEmbedding.sheafPullbackIso A).app 𝓕).hom).hom := sorry

/-- Restricting `𝓕.restrict U` further along `W ⊆ U` is canonically isomorphic to
`𝓕.restrict W`. -/
noncomputable def pullbackIso
    (𝓕 : TopCat.Sheaf A X) {W U : Opens X} (h : W ≤ U) :
    (TopCat.Sheaf.pullback A (homOfLE h)).obj (restrict 𝓕 U) ≅ restrict 𝓕 W :=
  (TopCat.Sheaf.pullbackComp (A := A) (homOfLE h) (inclusion U)).app 𝓕 ≪≫
    eqToIso (congrArg
      (fun f ↦ (TopCat.Sheaf.pullback A f).obj 𝓕)
      (homOfLE_comp_inclusion h))

/-- The canonical map from `𝓕.restrict U` to the pushforward of `𝓕.restrict W` along the
inclusion `W ⊆ U`. -/
noncomputable def toPushforward
    (𝓕 : TopCat.Sheaf A X) {W U : Opens X} (h : W ≤ U) :
    restrict 𝓕 U ⟶
      ((restrictionFunctor h).sheafPushforwardContinuous A
        (Opens.grothendieckTopology (space U))
        (Opens.grothendieckTopology (space W))).obj
        (restrict 𝓕 W) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction A (homOfLE h)).unit.app (restrict 𝓕 U)) ≫
    ((TopCat.Sheaf.pushforward A (homOfLE h)).mapIso (pullbackIso 𝓕 h)).hom

/-- Unfolding `toPushforward` exposes the pullback/pushforward adjunction unit followed by the
single transport to the directly restricted sheaf. -/
theorem toPushforward_def
    (𝓕 : TopCat.Sheaf A X) {W U : Opens X} (h : W ≤ U) :
    toPushforward 𝓕 h =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction A (homOfLE h)).unit.app (restrict 𝓕 U)) ≫
        ((TopCat.Sheaf.pushforward A (homOfLE h)).mapIso (pullbackIso 𝓕 h)).hom) := sorry

/-- The maps `toPushforward` for `T ⊆ W ⊆ U` compose to the map for the direct inclusion
`T ⊆ U`. -/
theorem toPushforward_comp
    (𝓕 : TopCat.Sheaf A X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    toPushforward 𝓕 hWU ≫
        ((restrictionFunctor hWU).sheafPushforwardContinuous A
          (Opens.grothendieckTopology (space U))
          (Opens.grothendieckTopology (space W))).map
        (toPushforward 𝓕 hTW) =
      toPushforward 𝓕 (hTW.trans hWU) := sorry

/-- Restricting from `X` to `U` and then applying `toPushforward` for `W ⊆ U` agrees with the
pullback/pushforward unit for the direct inclusion of `W` into `X`. -/
theorem toPushforward_comp_inclusion
    (𝓕 : TopCat.Sheaf A X) {W U : Opens X} (h : W ≤ U) :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A (inclusion U)).unit.app 𝓕) ≫
        (((Opens.map (inclusion U)).sheafPushforwardContinuous A
          (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (space U))).map
          (toPushforward 𝓕 h)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A (inclusion W)).unit.app 𝓕) := sorry

end Restriction

end TopCat.Sheaf.OpenSubset
