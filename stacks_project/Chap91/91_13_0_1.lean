/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Diagram
import StacksCheckRecall

/-!
# The deformation equation for ringed topoi

The bottom row is already the inverse-image row on the target site C: A' denotes
f⁻¹𝒪_{B'}, A denotes f⁻¹𝒪_B, M denotes f⁻¹𝒥, and j is its inclusion. Identifying the
underlying topoi of B and B' does not identify either of them with the target topos C.
A solution consists of a square-zero extension of 𝒪 by 𝒢 and a compatible ring map from
A' inducing the prescribed A-linear map c on kernels. No existence or uniqueness is asserted.
-/

@[expose] public section

open CategoryTheory
universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {A' A : Sheaf J CommRingCat.{w}}

/- 91.13.0.1: the square-zero extension diagram
0 ⟶ 𝒢 ⟶ middle ⟶ 𝒪 ⟶ 0 over 0 ⟶ f⁻¹𝒥 ⟶ f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B ⟶ 0.
Here A', A, M, and j are already pulled back to C. Both rows are short exact as additive
sheaves, their ring projections are locally surjective with square-zero kernels, and the
inclusions respect the quotient-module actions. The vertical maps induce the prescribed
map c and commute with the projections; this predicate does not assert a solution exists. -/
@[stacks 08UF] #check (SheafOfModules.RingedSite.SquareZeroExtension.IsSolution :
  (π : A' ⟶ A) → (M : SheafOfModules.{w} (Sheaf.ringSheafOfComm A)) →
  ((SheafOfModules.toSheaf (Sheaf.ringSheafOfComm A)).obj M ⟶
    (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj
      (Sheaf.ringSheafOfComm A')) →
  {O : Sheaf J CommRingCat.{w}} →
  (fSharp : A ⟶ O) → (G : SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) →
  (M ⟶ (SheafOfModules.restrictScalars (Sheaf.ringSheafOfCommMap fSharp)).obj G) →
  (middle : Sheaf J CommRingCat.{w}) → (middle ⟶ O) →
  ((SheafOfModules.toSheaf (Sheaf.ringSheafOfComm O)).obj G ⟶
    (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj
      (Sheaf.ringSheafOfComm middle)) →
  (A' ⟶ middle) → Prop)
