module

public import ReasLib.AlgebraicGeometry.FormalDeformation.EssentialSurjection
import StacksCheckRecall

/-!
# Essential surjections in `ArtinianLocalAlgCat`

A morphism in `C_Λ` is an essential surjection when it is surjective and
cancels surjectivity on the left.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Definition 90.3.9: A morphism `f : B ⟶ A` in `C_Λ` is an essential surjection
if `f` is surjective, and every morphism `g : C ⟶ B` in `C_Λ` such that `g ≫ f`
is surjective is itself surjective. -/
@[stacks 06GF] #check (ArtinianLocalAlgCat.IsEssentialSurjection :
  ∀ {B A : ArtinianLocalAlgCat Λ k}, (B ⟶ A) → Prop)
