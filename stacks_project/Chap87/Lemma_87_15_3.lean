/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_15_3_Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ObjectProperty
open ChosenBigFppfSite

universe u v

/- Lemma 87.15.3: Let `S` be a scheme. The category of formal algebraic spaces
over `S` has fibre products. -/
@[stacks 0AJ3] #check (IsFormalAlgebraicSpace.instHasPullbacks :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))],
    HasPullbacks (ObjectProperty.FullSubcategory
      fun X : Sheaf (𝒮.bigTopology S) (Type (max u v)) ↦ IsFormalAlgebraicSpace X))
