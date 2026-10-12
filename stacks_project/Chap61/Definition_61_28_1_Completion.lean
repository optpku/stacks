/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant.AdicCompletion
public import ReasLib.CategoryTheory.Sites.LocallyIsomorphic

/-!
# Completed constant module sheaves

Compatibility names for exact-power module quotients and their completed
constant sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Λ : Type w} [CommRing Λ]

/-- The quotient module `M / I ^ n M`, bundled as a `Λ`-module. -/
abbrev moduleQuotientStage (I : Ideal Λ) (M : ModuleCat.{w} Λ) (n : ℕ) :
    ModuleCat.{w} Λ :=
  Ideal.PowerQuotient.stage I M n

/-- The inverse system `n ↦ M / I ^ n M` of `Λ`-modules. -/
abbrev moduleQuotientSystem (I : Ideal Λ) (M : ModuleCat.{w} Λ) :
    ℕᵒᵖ ⥤ ModuleCat.{w} Λ :=
  ConstantSheaf.AdicCompletion.moduleSystem I M

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable (I : Ideal Λ)

/-- The inverse limit of the constant sheaves on `M / I ^ n M`. -/
abbrev constantAdicCompletion (M : ModuleCat.{w} Λ) : Sheaf J (ModuleCat.{w} Λ) :=
  ConstantSheaf.AdicCompletion.ofModule J I M

/-- Projection of the completed constant module sheaf onto its `n`th quotient stage. -/
abbrev constantAdicCompletion_π (M : ModuleCat.{w} Λ) (n : ℕ) :
    constantAdicCompletion J I M ⟶
      (constantSheaf J (ModuleCat.{w} Λ)).obj (moduleQuotientStage I M n) :=
  ConstantSheaf.AdicCompletion.ofModule_π J I M n

/-- The inverse limit of the constant sheaves on the quotients `Λ / I ^ n Λ`. -/
abbrev lambdaHat : Sheaf J (ModuleCat.{w} Λ) :=
  ConstantSheaf.AdicCompletion.ofModule J I (ModuleCat.of Λ Λ)

end AlgebraicGeometry.Scheme.ProEt
