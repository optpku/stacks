/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Bimodule
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable (A B : GradedAlgebraSheaf 𝒪 ℤ)
variable (M N : GradedBimodule 𝒪 A B)

/- Definition 24.8.1 (1): a graded `(A, B)`-bimodule on a ringed site `(C, 𝒪)` is a
`ℤ`-indexed family of `𝒪`-modules with `𝒪`-bilinear left `A`-action and right `B`-action,
associative on each side, mixed-associative, and unital for `1` in `A⁰` and `B⁰`. -/
@[stacks 0FR5] #check (SheafOfModules.RingedSite.GradedBimodule 𝒪 A B : Type (max (u + 1) (v + 1)))

/- The right multiplication is the packaged right graded `B`-module. -/
#check M.toRightModule

/- The left multiplication is the extra left graded `A`-action. -/
#check M.leftMul

/- Definition 24.8.1 (2): a homomorphism of graded `(A, B)`-bimodules is a degreewise family
of `𝒪`-module maps compatible with both multiplication maps. -/
@[stacks 0FR5] #check (SheafOfModules.RingedSite.GradedBimodule.Hom M N : Type (max u v))

end
