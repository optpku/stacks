/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Opens.Identity
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits

@[expose] public section

open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u

namespace TopCat.Sheaf

/-- Direct image of abelian sheaves along a self-map that preserves every open is
canonically the identity functor. -/
def pushforwardIsoOfPreimageEq {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U) :
    pushforward AddCommGrpCat.{u} g ≅ 𝟭 (X.Sheaf AddCommGrpCat.{u}) :=
  Functor.sheafPushforwardContinuousId' (Opens.mapIsoIdOfPreimageEq g hg)
    AddCommGrpCat.{u} (Opens.grothendieckTopology X)

/-- Inverse image of abelian sheaves along a self-map that preserves every open is
canonically the identity functor, as the unique left adjoint of the identity. -/
def pullbackIsoOfPreimageEq {X : TopCat.{u}} (g : X ⟶ X)
    (hg : ∀ U : Opens X, (Opens.map g).obj U = U) :
    pullback AddCommGrpCat.{u} g ≅ 𝟭 (X.Sheaf AddCommGrpCat.{u}) :=
  Adjunction.leftAdjointUniq
    ((pullbackPushforwardAdjunction AddCommGrpCat.{u} g).ofNatIsoRight
      (pushforwardIsoOfPreimageEq g hg))
    Adjunction.id

end TopCat.Sheaf
