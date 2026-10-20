module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.TransfiniteInjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.AbelianSheaf.InjectiveTower

universe w v u

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [UnivLE.{w, max u v}]

/- Lemma 19.7.1: a morphism into the `α`-stage of the bounded injective tower extends across a
monomorphism after passing to the next stage. Both stages belong to the one diagram ending at
`β`, so this successor lift composes directly with the canonical map to `J K β F`. -/
@[stacks 01DM] #check
  fun {β : Ordinal.{w}} (α : Below β)
      {G₁ G₂ F : Sheaf K AddCommGrpCat.{max u v}}
      (i : G₁ ⟶ G₂) [Mono i] (f : G₁ ⟶ belowStage K α F) ↦
    (existsLift K α i f : Nonempty (SuccessorLift K α i f))

/- The composable form used after Lemma 19.7.2: the `commSq` projection records the source
square, while `Factorization.top` records that a lift of a chosen factorization recovers the
original map at the top. -/
#check
  fun {β : Ordinal.{w}}
      {G₁ G₂ F : Sheaf K AddCommGrpCat.{max u v}}
      {φ : G₁ ⟶ J K β F} (e : Factorization K φ) {i : G₁ ⟶ G₂}
      (l : SuccessorLift K e.α i e.hom) ↦
    (Factorization.top K e l :
      i ≫ l.hom ≫ nextToTop K e.α F = φ)

#check @diagram
#check @stage
#check @J
#check @map
#check @toTop
#check @belowStage
#check @belowToTop
#check @nextStage
#check @belowToNext
#check @nextIso
#check @nextToTop
#check @belowToNext_comp_nextToTop
#check @Factorization
#check @Factorization.fac
#check @SuccessorLift
#check @SuccessorLift.commSq
#check @Factorization.top
#check @existsLift
