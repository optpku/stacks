module

public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap98.Definition_98_9_1_AlgebraHom
public import stacks_project.Chap98.Lemma_98_12_3_Associated
public import stacks_project.Chap98.Lemma_98_13_8_SmoothYoneda
public import stacks_project.Chap107.Definition_107_4_1_VersalRing
public import stacks_project.Chap107.Lemma_107_2_3
public import stacks_project.Chap107.Situation_107_2_1_Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Artin approximation of a versal ring by a smooth morphism

In Situation 107.2.1, if `A` is a versal ring at a finite-type field-valued
point and the stalk of `S` at the image of `Spec(k) ⟶ S` is a G-ring, then `A`
is realized as the completed stalk of a smooth finite-type 2-Yoneda chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.2.8: In Situation 107.2.1 let `x0 : Spec(k) ⟶ X` be a morphism
such that `Spec(k) ⟶ S` is of finite type with image `s`. Let `A` be a versal
ring to `X` at `x0`. If `O_{S,s}` is a G-ring, then there exist a smooth
morphism `U ⟶ X` whose source is a scheme and a point `u0 ∈ U` with residue
field `k` such that (1) `Spec(k) ⟶ U ⟶ X` coincides with `x0` and
(2) `O_{U,u0}^∧ ≅ A`. -/
@[stacks 0DR0]
theorem exists_smooth_of_isVersalRing {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)] :
    ∃ (W : SmoothFiniteTypeObject x0.structureHom x0.fiberObj)
      (φ : CompleteLocalSAlgebra.Hom A (completionSAlgebra W.toS W.u0)),
      Function.Bijective φ.hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
