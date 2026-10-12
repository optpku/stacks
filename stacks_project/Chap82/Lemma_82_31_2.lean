/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Lemma_82_31_2_Dual
public import stacks_project.Chap82.Remark_82_28_5_ChernClass

/-!
# Chern classes of dual modules on algebraic spaces

In the good setup of Situation 82.2.1, the degree-`i` Chern class of the dual
of a finite locally free module is `(-1) ^ i` times its degree-`i` Chern class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- Lemma 82.31.2: In Situation 82.2.1 let `X / B` be good. The Chern class
of the canonical dual of a finite locally free `𝒪_X`-module `E` satisfies
`c_i(Modules.dual E) = (-1)^i c_i(E)` in `A^i(X)`. -/
@[stacks 0ESD]
theorem chernClass_dual {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ) :
    chernClass δ f (Modules.dual E) i = ((-1 : ℤ) ^ i) • chernClass δ f E i := sorry

/-- Capping with the Chern class of the canonical dual is multiplication by
`(-1)^i` of capping with the original Chern class. -/
theorem chernClass_dual_cap {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (chernClass δ f (Modules.dual E) i).cap g k =
      ((-1 : ℤ) ^ i) • (chernClass δ f E i).cap g k := sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
