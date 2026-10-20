module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.TransfiniteInjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.AbelianSheaf.InjectiveTower

universe wI w v u

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [UnivLE.{w, max u v}]
variable {I : Type wI} [Small.{w} I]

/- Lemma 19.7.2: one ordinal works uniformly for a small family of abelian sheaves. Every map
into the top stage factors through a stage strictly below it in the same bounded tower. -/
@[stacks 01DN] #check
  fun (G : I → Sheaf K AddCommGrpCat.{max u v}) ↦
    (existsBound K G :
      ∃ β : Ordinal.{w},
        ∀ (F : Sheaf K AddCommGrpCat.{max u v}) (i : I)
          (φ : G i ⟶ J K β F),
          Nonempty (Factorization K φ))

/- Applying the uniform bound returns a factorization object with an explicit earlier stage,
map, and factorization equation. -/
#check
  fun {β : Ordinal.{w}} (G : I → Sheaf K AddCommGrpCat.{max u v})
      (h : IsBound K G β) (F : Sheaf K AddCommGrpCat.{max u v}) (i : I)
      (φ : G i ⟶ J K β F) ↦
    (IsBound.apply K h F i φ : Nonempty (Factorization K φ))

/- Downstream composable form of Lemmas 19.7.2 and 19.7.1: a bound supplies a factorization and
a successor lift across any monomorphism; `Factorization.top` then supplies the equation back to
the same top map. -/
#check
  fun {β : Ordinal.{w}} (G : I → Sheaf K AddCommGrpCat.{max u v})
      (h : IsBound K G β) (F : Sheaf K AddCommGrpCat.{max u v}) (i : I)
      (φ : G i ⟶ J K β F) {G₂ : Sheaf K AddCommGrpCat.{max u v}}
      (m : G i ⟶ G₂) [Mono m] ↦
    (IsBound.existsLift K h F i φ m :
      ∃ e : Factorization K φ,
        Nonempty (SuccessorLift K e.α m e.hom))

#check @existsSuccLimitBound
#check @existsSmallnessBound
#check @IsBound
#check @IsBound.apply
#check @IsBound.existsLift
#check @Factorization
#check @Factorization.fac
#check @Factorization.top
#check @SuccessorLift
#check @SuccessorLift.commSq
