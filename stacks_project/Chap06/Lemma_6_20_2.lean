/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Mathlib's site-generic adjunction is the reusable owner, and also supports sheaves of modules
over possibly noncommutative rings. -/
recall SheafOfModules.pullbackPushforwardAdjunction

variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable (p : 𝒪₁ ⟶ 𝒪₂)
variable
  (𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪₁))
  (ℱ : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪₂))

/- Lemma 6.20.2: under the Stacks convention that rings are commutative with `1`, extension of
scalars along `p : 𝒪₁ ⟶ 𝒪₂` is left adjoint to restriction of scalars. -/
@[stacks 008A "change of rings is left adjoint to restriction of scalars"]
#check SheafOfModules.pullbackPushforwardAdjunction
  (TopCat.Sheaf.commRingSheafHomOverId p)

/- The source's canonical bijection is the inverse hom-equivalence of this adjunction. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (TopCat.Sheaf.commRingSheafHomOverId p)).homEquiv 𝒢 ℱ).symm :
    (𝒢 ⟶
      (SheafOfModules.pushforward (TopCat.Sheaf.commRingSheafHomOverId p)).obj ℱ) ≃
        ((SheafOfModules.pullback (TopCat.Sheaf.commRingSheafHomOverId p)).obj 𝒢 ⟶ ℱ))
