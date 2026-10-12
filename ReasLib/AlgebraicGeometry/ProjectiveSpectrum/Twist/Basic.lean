/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Integral families of module sheaves on projective spectra

This file provides explicit evaluation and tensor twisting for an already constructed
integer-indexed family of module sheaves on a projective spectrum.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

namespace AlgebraicGeometry

variable {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  {calA : Nat -> sigma} [GradedRing calA]

/-- An explicitly supplied integer-indexed family of module sheaves on a projective spectrum. -/
abbrev ProjTwistFamily (calA : Nat -> sigma) [GradedRing calA] :=
  Int -> (Proj calA).Modules

namespace ProjTwistFamily

/-- The module sheaf of index `n` in an integral family on a projective spectrum. -/
def twist (P : ProjTwistFamily calA) (n : Int) : (Proj calA).Modules :=
  P n

/-- Evaluation at `n` gives the module sheaf of index `n`. -/
theorem twist_def (P : ProjTwistFamily calA) (n : Int) :
    P.twist n = P n := rfl

/-- Tensor a module sheaf with the member of index `n` of an integral family. -/
def tensorTwist [MonoidalCategory (Proj calA).Modules]
    (P : ProjTwistFamily calA) (F : (Proj calA).Modules) (n : Int) :
    (Proj calA).Modules :=
  tensorObj F (P.twist n)

/-- Tensor twisting is tensor product with the member of the given index. -/
theorem tensorTwist_def [MonoidalCategory (Proj calA).Modules]
    (P : ProjTwistFamily calA) (F : (Proj calA).Modules) (n : Int) :
    P.tensorTwist F n = tensorObj F (P.twist n) := rfl

end ProjTwistFamily

end AlgebraicGeometry
