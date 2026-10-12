/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.SupportedQuotient
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Definition
public import ReasLib.Topology.Sheaves.Pullback.Composition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorization through a supported quotient

A factorization of the structure-sheaf map through a locally surjective quotient sheaf determines
a unique morphism to the locally ringed space carried by its support. This file exposes the
underlying map, its inverse-image and pushforward sheaf maps, and the resulting locally ringed-space
morphism as explicit data. Support membership, continuity, localness, and the universal-property
laws remain separate proof obligations.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.SupportedQuotient

variable {X Y : LocallyRingedSpace.{u}} (Q : Presentation X) (f : Y ⟶ X)

/-- Every point of the source maps into the support of a quotient sheaf through which the
structure-sheaf map factors. -/
@[stacks 01HP "supported quotient lift lands in the support"]
theorem map_mem_support
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f)
    (y : Y) : f.base y ∈ support Q := sorry

/-- The pointwise lift to the quotient support is continuous. -/
@[stacks 01HP "continuity of the supported quotient base lift"]
theorem continuous_liftBase
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    Continuous fun y : Y =>
      (⟨f.base y, map_mem_support Q f alpha h_alpha y⟩ : carrier Q) := sorry

/-- The explicit continuous map from the source to the support of the quotient sheaf. -/
@[stacks 01HP "base map of the supported quotient lift"]
noncomputable def liftBase
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    Y.toTopCat ⟶ carrier Q :=
  TopCat.ofHom
    ⟨fun y => ⟨f.base y, map_mem_support Q f alpha h_alpha y⟩,
      continuous_liftBase Q f alpha h_alpha⟩

/-- The lifted base map followed by the support inclusion is the original base map. -/
@[simp, stacks 01HP "supported quotient base-lift computation"]
theorem liftBase_inclusion
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    liftBase Q f alpha h_alpha ≫ inclusion Q = f.base := sorry

/-- The inverse-image structure-sheaf map of the supported quotient lift. It is obtained by
pulling the quotient sheaf back along the lifted base map and then applying the given quotient
factorization. -/
@[stacks 01HP "inverse-image map of the supported quotient lift"]
noncomputable def inverseImageLiftMap
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    (TopCat.Sheaf.pullback CommRingCat.{u}
      (liftBase Q f alpha h_alpha)).obj (structureSheaf Q) ⟶ Y.𝒪 :=
  (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
      (liftBase Q f alpha h_alpha) (inclusion Q)).hom.app Q.sheaf ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      f.base).homEquiv Q.sheaf Y.𝒪).symm alpha

/-- The pushforward form of the structure-sheaf map of the supported quotient lift. -/
@[stacks 01HP "structure-sheaf map of the supported quotient lift"]
noncomputable def liftSheafMap
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    structureSheaf Q ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u}
        (liftBase Q f alpha h_alpha)).obj Y.𝒪 :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (liftBase Q f alpha h_alpha)).homEquiv (structureSheaf Q) Y.𝒪
      (inverseImageLiftMap Q f alpha h_alpha)

/-- The presheafed-space morphism underlying the supported quotient lift. -/
@[stacks 01HP "supported quotient presheafed-space lift"]
noncomputable def liftToHom
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    Y.toPresheafedSpace ⟶ (space Q).toPresheafedSpace where
  base := liftBase Q f alpha h_alpha
  c := (liftSheafMap Q f alpha h_alpha).hom

/-- The stalk maps of the supported quotient lift are local ring homomorphisms. -/
@[stacks 01HP "supported quotient lift stalk local homomorphism"]
theorem liftToHom_isLocalHom
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) (y : Y) :
    IsLocalHom ((liftToHom Q f alpha h_alpha).stalkMap y).hom := sorry

/-- The canonical morphism to the supported quotient induced by a factorization of the
structure-sheaf map. -/
@[stacks 01HP "canonical supported quotient lift"]
noncomputable def lift
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    Y ⟶ space Q where
  toHom := liftToHom Q f alpha h_alpha
  prop := liftToHom_isLocalHom Q f alpha h_alpha

/-- Forgetting localness recovers the explicit presheafed-space lift. -/
@[simp, stacks 01HP "supported quotient lift underlying morphism"]
theorem lift_toHom
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    (lift Q f alpha h_alpha).toHom = liftToHom Q f alpha h_alpha := sorry

/-- The base map of the supported quotient lift is the explicit subtype-valued lift. -/
@[simp, stacks 01HP "supported quotient lift underlying map"]
theorem lift_base
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    (lift Q f alpha h_alpha).base = liftBase Q f alpha h_alpha := sorry

/-- The supported quotient lift factors the original morphism. -/
@[reassoc, simp, stacks 01HP "supported quotient lift computation"]
theorem lift_comp_ι
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    lift Q f alpha h_alpha ≫ ι Q = f := sorry

/-- The canonical supported quotient lift is the unique morphism over the ambient space. -/
@[stacks 01HP "supported quotient lift uniqueness"]
theorem lift_unique
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f)
    (g : Y ⟶ space Q) (hg : g ≫ ι Q = f) :
    g = lift Q f alpha h_alpha := sorry

/-- A quotient-sheaf factorization induces a unique locally ringed-space morphism over the
ambient space. -/
@[stacks 01HP "supported quotient universal property"]
theorem existsUnique_lift
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    ∃! g : Y ⟶ space Q, g ≫ ι Q = f := sorry

/-- A quotient-sheaf factorization induces a morphism to the supported quotient. -/
@[stacks 01HP "supported quotient lift existence"]
theorem exists_lift
    (alpha : Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪)
    (h_alpha : Q.projection ≫ alpha =
      Hom.commRingSheafPushforwardMap f) :
    ∃ g : Y ⟶ space Q, g ≫ ι Q = f := sorry

end AlgebraicGeometry.LocallyRingedSpace.SupportedQuotient
