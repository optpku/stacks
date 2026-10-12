/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified
public import stacks_project.Chap76.«76_15_0_1_Universal»

/-!
# Unramified local complete intersection morphisms of algebraic spaces

A local complete intersection morphism of algebraic spaces is unramified if and
only if it is formally unramified, and in that case the conormal sheaf of any
universal first-order thickening is finite locally free.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsLocalCompleteIntersection

/-- Lemma 76.48.12 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a local
complete intersection morphism of algebraic spaces over `S`. Then `f` is
unramified if and only if `f` is formally unramified. -/
@[stacks 06CB]
theorem unramified_iff_formallyUnramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f] :
    Unramified f ↔ FormallyUnramified f :=
  sorry

/-- A formally unramified local complete intersection morphism of algebraic
spaces is unramified. -/
instance unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocalCompleteIntersection f] [FormallyUnramified f] : Unramified f :=
  sorry

end IsLocalCompleteIntersection

namespace IsUniversalFirstOrder

/-- Lemma 76.48.12 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a formally
unramified local complete intersection morphism of algebraic spaces over `S`.
Then the conormal sheaf `Hom.conormalSheaf i` of any universal first-order
thickening `i` of `X` over `Y` is finite locally free on `X`. -/
@[stacks 06CB]
instance conormalSheaf_isFiniteLocallyFree {S : Scheme.{u}}
    {X Y X' : AlgebraicSpace S} (i : X ⟶ X') (f : X' ⟶ Y)
    [FormallyUnramified (i ≫ f)] [IsLocalCompleteIntersection (i ≫ f)]
    [IsUniversalFirstOrder i f] : (Hom.conormalSheaf i).IsFiniteLocallyFree :=
  sorry

end IsUniversalFirstOrder

end AlgebraicGeometry.AlgebraicSpace
