module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ProjectiveSpace
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.39.3: for a locally finite type morphism `f : X ⟶ S` and an ample invertible
module `L` on `X`, every sufficiently high tensor power of `L` is the pullback of the
tautological module along an immersion over `S` into a finite relative projective space. -/
@[stacks 01VS] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.eventualProjectiveSpacePresentation :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L] [LocallyOfFiniteType f],
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
          ∃ e : RingedSpace.TensorPower.sheaf L d ≅
              (Scheme.Modules.pullback i).obj P.tautologicalSheaf,
            IsImmersion i ∧ i ≫ P.hom = f)
