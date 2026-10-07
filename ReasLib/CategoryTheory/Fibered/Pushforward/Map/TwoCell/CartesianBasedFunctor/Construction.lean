module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.Fibered
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell.Functor.Localized
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian pushforward two-cell construction

This file packages a raw localized pushforward transformation as a vertical transformation of
cartesian based functors and exposes its forgetful computations.
-/

@[expose] public section

universe uC uD uS uT vC vD vS vT

namespace CategoryTheory.CartesianBasedFunctor.Pushforward

open Limits
open scoped Bicategory Functor

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C} [p.IsFibered] [q.IsFibered]
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- The raw localized pushforward `2`-cell is over the identity of the target base for the
explicitly bundled cartesian endpoints. -/
@[stacks 04WI "cartesian pushforward two-cell over the base"]
theorem map₂.overId {F G : CartesianBasedFunctor p q}
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (hG : Functor.Pushforward.sourceMap.inverts u G) (eta : F ⟶ G) :
    eqToHom (map u F hp hq hF).toBasedFunctor.w.symm ≫
        Functor.whiskerRight (Functor.Pushforward.map₂ u hF hG eta)
          (u.pushforwardProjection q hq) ≫
          eqToHom (map u G hp hq hG).toBasedFunctor.w =
      𝟙 (u.pushforwardProjection p hp) := sorry

/-- Pushforward of a morphism between cartesian based functors, with both endpoint inversion
proofs explicit. -/
@[stacks 04WI "cartesian pushforward two-cell"]
noncomputable def map₂ {F G : CartesianBasedFunctor p q}
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (hG : Functor.Pushforward.sourceMap.inverts u G) (eta : F ⟶ G) :
    map u F hp hq hF ⟶ map u G hp hq hG :=
  CartesianBasedFunctor.homMk
    (BasedNatTrans.ofOverId (Functor.Pushforward.map₂ u hF hG eta)
      (map₂.overId u hp hq hF hG eta))

/-- The cartesian pushforward `2`-cell determined by a bundled inversion choice. This is the
proof-bundled counterpart of the explicit `map₂` owner and avoids repeatedly unpacking endpoint
and morphism inversion fields in consumers. -/
@[stacks 04WI "cartesian pushforward two-cell from inversion choice"]
noncomputable def map₂.ofInversionChoice
    {F G : CartesianBasedFunctor p q}
    (h : InversionChoice u p q) (eta : F ⟶ G) :
    map.ofInversionChoice u F h ⟶ map.ofInversionChoice u G h :=
  map₂ u h.source h.target (h.inverts F) (h.inverts G) eta

/-- The bundled cartesian pushforward `2`-cell preserves identities. -/
@[simp, stacks 04WI "cartesian pushforward bundled two-cell identity"]
theorem map₂.ofInversionChoice.id
    (h : InversionChoice u p q) (F : CartesianBasedFunctor p q) :
    map₂.ofInversionChoice u h (𝟙 F) =
      𝟙 (map.ofInversionChoice u F h) := sorry

/-- The bundled cartesian pushforward `2`-cell preserves vertical composition. -/
@[simp, stacks 04WI "cartesian pushforward bundled two-cell composition"]
theorem map₂.ofInversionChoice.comp
    (h : InversionChoice u p q) {F G H : CartesianBasedFunctor p q}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂.ofInversionChoice u h (eta ≫ theta) =
      map₂.ofInversionChoice u h eta ≫ map₂.ofInversionChoice u h theta := sorry

/-- The based natural transformation underlying cartesian pushforward is the explicitly
constructed over-identity transformation. -/
@[simp, stacks 04WI "cartesian pushforward two-cell based form"]
theorem map₂.toBasedNatTrans {F G : CartesianBasedFunctor p q}
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (hG : Functor.Pushforward.sourceMap.inverts u G) (eta : F ⟶ G) :
    CartesianBasedFunctor.toBasedNatTrans (map₂ u hp hq hF hG eta) =
      BasedNatTrans.ofOverId
        (F := (map u F hp hq hF).toBasedFunctor)
        (G := (map u G hp hq hG).toBasedFunctor)
        (Functor.Pushforward.map₂ u hF hG eta)
        (map₂.overId u hp hq hF hG eta) := sorry

/-- The total natural transformation underlying cartesian pushforward is the raw localized
pushforward transformation. -/
@[simp, stacks 04WI "cartesian pushforward two-cell total form"]
theorem map₂.toNatTrans {F G : CartesianBasedFunctor p q}
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (hq : Functor.Pushforward.ProjectionChoice u q)
    (hF : Functor.Pushforward.sourceMap.inverts u F)
    (hG : Functor.Pushforward.sourceMap.inverts u G) (eta : F ⟶ G) :
    (CartesianBasedFunctor.toBasedNatTrans (map₂ u hp hq hF hG eta)).toNatTrans =
      Functor.Pushforward.map₂ u hF hG eta := sorry

end CategoryTheory.CartesianBasedFunctor.Pushforward

-- Data audit: the underlying localized natural transformation and both endpoint choices are
-- explicit; `sorryAx` may occur only in over-base and naturality proof fields.
