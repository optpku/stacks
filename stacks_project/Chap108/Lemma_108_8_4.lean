/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_8_4_Product
public import stacks_project.Chap108.Lemma_108_8_4_Stack

/-!
# Lemma 108.8.4

The inertia stack of the Picard stack of a morphism of algebraic spaces with the
base-change structure-sheaf isomorphism hypothesis is `𝔾ₘ[S] ×_S Pic_{X/B}`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open StackOver.Groupoids
open StackOver.Groupoids.Hom

/-- Lemma 108.8.4: if `f : X ⟶ B` is a morphism of algebraic spaces over `S` such that
`f_{T,*} O_{X_T} ≅ O_T` for every scheme `T` over `B`, then the inertia stack of
`picardStack f` is equal to `𝔾ₘ[S] ×_S picardStack f` as a stack in groupoids over
`(Sch/S)_fppf`. -/
@[stacks 0DNH]
theorem inertia_mulGroupProduct {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsEquivalence (Picard.inertiaMulGroupHom f :
      inertia (picardStack f) ⟶ Picard.mulGroupProduct f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
