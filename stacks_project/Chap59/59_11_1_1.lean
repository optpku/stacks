/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafCondition
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

/- 59.11.1.1 (03NL): sections over the base, the product of sections over an
   indexed family, and the product over pairwise fiber products form the sheaf
   equalizer diagram. -/
@[stacks 03NL] #check (AlgebraicGeometry.Scheme.Etale.sheafCondition :
    ∀ {U : Scheme.{u}} {ι : Type v} [Small.{u} ι]
      {X : ι → Scheme.{u}} (φ : ∀ i, X i ⟶ U)
      [(Presieve.ofArrows X φ).HasPairwisePullbacks]
      (F : Scheme.{u}ᵒᵖ ⥤ Type u),
      (Presieve.ofArrows X φ).IsSheafFor F ↔
        Nonempty (IsLimit
          (Fork.ofι (Equalizer.Presieve.Arrows.forkMap F X φ)
            (Equalizer.Presieve.Arrows.w F X φ))))
