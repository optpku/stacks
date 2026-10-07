module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.Algebra.DirectSum.Internal

/-!
# Global sections of twists on projective spectra

An explicit multiplication on an integral family of twists induces an action of the
nonnegative-graded global sections of the family on the integer-graded global sections of a
twisted module.
-/

@[expose] public section

open CategoryTheory
open Opposite
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.ProjTwistGlobalSections

variable {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
  [AddSubgroupClass sigma A]
variable (calA : Nat -> sigma) [GradedRing calA]

/-- The degree-`n` global sections of an integral family of twists. -/
abbrev degree (P : ProjTwistFamily calA) (n : Nat) : Type _ :=
  Γ(P.twist (n : Int), ⊤)

/-- The degree-`m` global sections of a module tensored with an integral family of twists. -/
abbrev twistedDegree (P : ProjTwistFamily calA) (F : (Proj calA).Modules)
    (m : Int) : Type _ :=
  Γ(P.tensorTwist F m, ⊤)

/-- A homogeneous twist section acts additively on a homogeneous twisted-module section. -/
noncomputable def homogeneousAction
    (P : ProjTwistFamily calA) (mul : P.Multiplication)
    (F : (Proj calA).Modules) (n : Nat) (m : Int) :
    degree calA P n →+
      twistedDegree calA P F m →+
        twistedDegree calA P F ((n : Int) + m) where
  toFun x :=
    ((projSheafTwistMul calA P mul F (n : Int) m).val.app (op ⊤)).hom.toAddMonoidHom.comp
      (SheafOfModules.RingedSite.tensorSectionLinear
        (Proj calA).sheaf (P.twist (n : Int)) (P.tensorTwist F m) (op ⊤) x).toAddMonoidHom
  map_zero' := sorry
  map_add' := sorry

/-- The curried additive action of the direct sum of nonnegative twist sections on the direct
sum of all twisted-module sections. -/
noncomputable def directSumActionHom
    (P : ProjTwistFamily calA) (mul : P.Multiplication)
    (F : (Proj calA).Modules) :
    (⨁ n : Nat, degree calA P n) →+
      ((⨁ m : Int, twistedDegree calA P F m) →+
        (⨁ m : Int, twistedDegree calA P F m)) :=
  DirectSum.toAddMonoid fun n =>
    { toFun := fun x =>
        DirectSum.toAddMonoid fun m =>
          (DirectSum.of (twistedDegree calA P F) ((n : Int) + m)).comp
            (homogeneousAction calA P mul F n m x)
      map_zero' := sorry
      map_add' := sorry }

/-- The action map from a pair of graded global-section sums to the twisted-section sum. -/
noncomputable def directSumAction
    (P : ProjTwistFamily calA) (mul : P.Multiplication)
    (F : (Proj calA).Modules) :
    ((⨁ n : Nat, degree calA P n) ×
      (⨁ m : Int, twistedDegree calA P F m)) →
        (⨁ m : Int, twistedDegree calA P F m) :=
  fun xy => directSumActionHom calA P mul F xy.1 xy.2

/-- Acting on two pure summands places the homogeneous action in the sum of their degrees. -/
theorem directSumAction_of_of
    (P : ProjTwistFamily calA) (mul : P.Multiplication)
    (F : (Proj calA).Modules) (n : Nat) (m : Int)
    (x : degree calA P n) (y : twistedDegree calA P F m) :
    directSumAction calA P mul F
        (DirectSum.of (degree calA P) n x,
          DirectSum.of (twistedDegree calA P F) m y) =
      DirectSum.of (twistedDegree calA P F) ((n : Int) + m)
        (homogeneousAction calA P mul F n m x y) := sorry

end AlgebraicGeometry.ProjTwistGlobalSections
