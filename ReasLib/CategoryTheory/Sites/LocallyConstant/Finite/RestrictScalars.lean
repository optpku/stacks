/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite

/-!
# Finite locally constant modules after restriction of scalars

This file records the coefficient-sensitive version of finite-type local constancy.  A sheaf of
`R`-modules has this property along `R →+* S` when its local constant models are restrictions of
finite `S`-modules.
-/

@[expose] public section

universe u v w w'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type w} {S : Type w'} [Ring R] [Ring S]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max w w'} R)]

/-- A sheaf of `R`-modules is finite-type locally constant along `f : R →+* S` when its local
constant models are restrictions of finite `S`-modules. -/
abbrev IsFiniteTypeLocallyConstantRestrictedModule (f : R →+* S)
    (F : Sheaf J (ModuleCat.{max w w'} R)) : Prop :=
  IsLocallyConstantWith (J := J)
    (fun M : ModuleCat.{max w w'} R ↦
      ∃ N : ModuleCat.{max w w'} S, Module.Finite S N ∧
        Nonempty (M ≅ (ModuleCat.restrictScalars f).obj N)) F

/-- The object property of finite-type locally constant `R`-module sheaves whose local models
come from finite `S`-modules by restriction along `f : R →+* S`. -/
abbrev finiteTypeLocallyConstantRestrictedModule (J : GrothendieckTopology C)
    (f : R →+* S)
    [hJ : ∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max w w'} R)] :
    ObjectProperty (Sheaf J (ModuleCat.{max w w'} R)) :=
  fun F ↦ IsFiniteTypeLocallyConstantRestrictedModule (J := J) f F

namespace IsFiniteTypeLocallyConstantRestrictedModule

/-- The finite constant `S`-module charts supplied by a sheaf that is finite-type locally
constant after restriction of scalars along `f`. -/
theorem existsFiniteConstantCover (f : R →+* S)
    (F : Sheaf J (ModuleCat.{max w w'} R))
    [IsFiniteTypeLocallyConstantRestrictedModule (J := J) f F] (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, ∃ N : ModuleCat.{max w w'} S, Module.Finite S N ∧
        Nonempty (F.over (X i).left ≅
          (constantSheaf (J.over (X i).left) (ModuleCat.{max w w'} R)).obj
            ((ModuleCat.restrictScalars f).obj N)) := sorry

end IsFiniteTypeLocallyConstantRestrictedModule

end CategoryTheory.Sheaf
