/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.Affine
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.PuncturedAffineSpace
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Exercise 111.42.6 (1): the canonical morphism from punctured affine space to projective space
is affine and surjective. -/
@[stacks 0D8V] #check
  (AlgebraicGeometry.PuncturedAffineSpace.toProjectiveSpace_isAffineHom :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      IsAffineHom (AlgebraicGeometry.PuncturedAffineSpace.toProjectiveSpace A n))
#check
  (AlgebraicGeometry.PuncturedAffineSpace.toProjectiveSpace_surjective :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      Surjective (AlgebraicGeometry.PuncturedAffineSpace.toProjectiveSpace A n))

/- Exercise 111.42.6 (2): the pushforward of the structure sheaf is the coproduct of all
integer twists of the projective-space structure sheaf. -/
@[stacks 0D8V] #check
  (AlgebraicGeometry.PuncturedAffineSpace.pushforward_unit_coproduct_twists :
    ∀ (A : Type u) [CommRing A] (n : ℕ),
      IsIsomorphic
        ((Scheme.Modules.pushforward
            (AlgebraicGeometry.PuncturedAffineSpace.toProjectiveSpace A n)).obj
          (SheafOfModules.unit
              (AlgebraicGeometry.PuncturedAffineSpace.puncturedOpen
                  (AlgebraicGeometry.PuncturedAffineSpace.projectiveIndex n) A).toScheme.ringCatSheaf :
            (AlgebraicGeometry.PuncturedAffineSpace.puncturedOpen
                (AlgebraicGeometry.PuncturedAffineSpace.projectiveIndex n) A).toScheme.Modules))
        (∐ fun d : ℤ ↦ ProjectiveSpace.twistingSheaf A n d))

/- Exercise 111.42.6 (3): the graded-module version identifies the pushforward of the restricted
associated sheaf with the coproduct of the associated sheaves of all grading shifts. -/
@[stacks 0D8V] #check
  (AlgebraicGeometry.PuncturedAffineSpace.pushforward_tildeRestrict_coproduct_shifts :
    ∀ (A : Type u) [CommRing A] (n : ℕ)
      (M : Type u) [AddCommGroup M] [Module A M]
      [Module
        (AlgebraicGeometry.PuncturedAffineSpace.coordinateRing (Fin (n + 1)) A) M]
      (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul (ProjectiveSpace.grading A n) ℳ],
      IsIsomorphic
        ((Scheme.Modules.pushforward
            (AlgebraicGeometry.PuncturedAffineSpace.toProjectiveSpace A n)).obj
          (AlgebraicGeometry.PuncturedAffineSpace.tildeRestrict A n M))
        (∐ fun d : ℤ ↦
          Proj.AssociatedModule.sheaf (ProjectiveSpace.grading A n)
            (GradedModule.shiftGrading ℳ d)))
