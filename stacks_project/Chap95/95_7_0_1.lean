/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap95.«95_7_0_1_Hom»
public import stacks_project.Chap95.«95_7_0_1_Spaces»

/-!
# Morphisms of Spaces

The Hom-set in Spaces from `X / U` to `Y / V` is the coproduct over morphisms
`g : U ⟶ V` of Hom-sets in Spaces / U from `X` to `U ×_{g, V} Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (pX : X ⟶ ofOver U) (pY : Y ⟶ ofOver V)

/- 95.7.0.1: morphisms of Spaces from `X / U` to `Y / V` are the coproduct, over
base morphisms `g : U ⟶ V` in `Over S`, of morphisms over `ofOver U` from `X` to
the fibre product `U ×_{g, V} Y`. -/
@[stacks 04U8] #check
  (CategoryTheory.Comma.homEquivSigmaPullback (ofOverFunctor S) (Spaces.mk pX) (Spaces.mk pY) :
    (Spaces.mk pX ⟶ Spaces.mk pY) ≃
      Σ g : U ⟶ V, (Over.mk pX ⟶ Spaces.pullbackSlice g pY))
