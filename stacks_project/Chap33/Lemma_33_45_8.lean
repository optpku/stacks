/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.EffectiveCartier
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.45.8: intersecting a positive-dimensional proper closed subscheme with
invertible modules whose first restriction cuts out an effective Cartier divisor equals the
finite-difference intersection coefficient of the restricted tail on that divisor. -/
@[stacks 0BEU] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number_eq_tailPullback_of_effectiveCartierDivisor :
    ∀ (k : Type u) [Field k] {d : ℕ} (hd : 0 < d)
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (hZdim : topologicalKrullDim Z.subscheme = d)
      (L : Fin d → X.Modules) [∀ j : Fin d, Scheme.Modules.Invertible (L j)]
      (D : Z.subscheme.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      [HasExt (Sheaf (Opens.grothendieckTopology D.subscheme.carrier) AddCommGrpCat.{u})],
      ((Scheme.Modules.pullback Z.subschemeι).obj (L ⟨0, hd⟩) ≅ D.associatedSheaf) →
        AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim L =
          AlgebraicGeometry.Scheme.Modules.Intersection.finiteDifferenceNumber
            k (Z.subschemeι ≫ f) D
            (AlgebraicGeometry.Scheme.Modules.Intersection.tailPullback hd Z L))
