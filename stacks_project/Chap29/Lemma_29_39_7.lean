/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ProjectiveSpace
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.39.7: For a finite-type morphism, an invertible module is relatively ample if and
only if, locally on the base, a positive tensor power is pulled back from the tautological module
along an immersion into a finite relative projective space. -/
@[stacks 02NR] #check
  (AlgebraicGeometry.RelativelyAmple.iff_exists_openCover_projectiveSpacePresentation_of_finiteType :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
        [Scheme.Modules.Invertible L] [Scheme.Hom.FiniteType f],
      RelativelyAmple f L ↔
        ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ j : 𝒰.I₀,
          ∃ d : ℕ, 1 ≤ d ∧
            ∃ (n : ℕ) (P : ProjectiveSpaceOver ((𝒰.f j).opensRange).toScheme n)
                (i : (f ⁻¹ᵁ (𝒰.f j).opensRange).toScheme ⟶ P.scheme),
              ∃ e : Scheme.Modules.restrict (RingedSpace.TensorPower.sheaf L d)
                  ((f ⁻¹ᵁ (𝒰.f j).opensRange).ι) ≅
                    (Scheme.Modules.pullback i).obj P.tautologicalSheaf,
                IsImmersion i ∧ i ≫ P.hom = f ∣_ (𝒰.f j).opensRange)
