/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.CategoryTheory.Comma.Pullback
public import stacks_project.Chap95.«95_7_0_1_Spaces»

/-!
# Hom-sets in Spaces

A morphism `X / U ⟶ Y / V` in `Spaces` is a commutative square. Equivalently, it is a
base morphism `g : U ⟶ V` together with a morphism over `ofOver U` from `X` to the fibre
product `U ×_{g, V} Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- The fibre product `Y ×_{V, g} U` over `ofOver U`, with its second projection. -/
def pullbackSlice {S : Scheme.{u}} {U V : Over S} (g : U ⟶ V) {Y : AlgebraicSpace S}
    (pY : Y ⟶ ofOver V) : Over (ofOver U) :=
  (Over.pullback ((ofOverFunctor S).map g)).obj (Over.mk pY)

/-- The algebraic-space fibre product `Y ×_{V, g} U` underlying the slice pullback. -/
def pullbackObj {S : Scheme.{u}} {U V : Over S} (g : U ⟶ V) {Y : AlgebraicSpace S}
    (pY : Y ⟶ ofOver V) : AlgebraicSpace S :=
  (pullbackSlice g pY).left

/-- The morphism `X ⟶ Y ×_{V, g} U` induced by a Spaces morphism with base map `g`. -/
def toSigmaLeft {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) (pY : Y ⟶ ofOver V) (φ : mk pX ⟶ mk pY) :
    X ⟶ pullbackObj φ.right pY :=
  (Comma.homEquivSigmaPullback (ofOverFunctor S) (mk pX) (mk pY) φ).2.left

end AlgebraicGeometry.AlgebraicSpace.Spaces
