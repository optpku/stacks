/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Multiplication of twists on projective spectra

An explicit multiplication on an integral family of twists induces the corresponding action of
one twist on a module tensored with another twist.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace AlgebraicGeometry

variable {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
  [AddSubgroupClass sigma A]
variable {calA : Nat -> sigma} [GradedRing calA]

namespace ProjTwistFamily

/-- A multiplication on an integral twist family assigns a morphism from the tensor product of
the twists of indices `n` and `m` to the twist of index `n + m`. -/
abbrev Multiplication [MonoidalCategory (Proj calA).Modules] (P : ProjTwistFamily calA) :=
  forall n m : Int, tensorObj (P.twist n) (P.twist m) ⟶ P.twist (n + m)

end ProjTwistFamily

section

variable (calA : Nat -> sigma) [GradedRing calA]
variable [MonoidalCategory (Proj calA).Modules] [BraidedCategory (Proj calA).Modules]

/-- Multiplication on an integral twist family induces a morphism from a twist tensored with a
twisted module to the module twisted by the sum of the two indices. -/
noncomputable def projSheafTwistMul
    (twist : ProjTwistFamily calA) (twistMul : twist.Multiplication)
    (F : (Proj calA).Modules) (n m : Int) :
    (tensorObj (twist n) (tensorObj F (twist m)) : (Proj calA).Modules) ⟶
      tensorObj F (twist (n + m)) :=
  (α_ (twist n) F (twist m)).inv ≫
    ((β_ (twist n) F).hom ⊗ₘ 𝟙 (twist m)) ≫
    (α_ F (twist n) (twist m)).hom ≫
    (𝟙 F ⊗ₘ twistMul n m)

/-- The twist-action morphism is the associator-braiding composite followed by multiplication of
the two twist factors. -/
theorem projSheafTwistMul_def
    (twist : ProjTwistFamily calA) (twistMul : twist.Multiplication)
    (F : (Proj calA).Modules) (n m : Int) :
    projSheafTwistMul calA twist twistMul F n m =
      (α_ (twist n) F (twist m)).inv ≫
        ((β_ (twist n) F).hom ⊗ₘ 𝟙 (twist m)) ≫
        (α_ F (twist n) (twist m)).hom ≫
        (𝟙 F ⊗ₘ twistMul n m) := sorry

end

end AlgebraicGeometry
