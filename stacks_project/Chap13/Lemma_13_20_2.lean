/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Bounded.Global
import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Resolution
import StacksCheckRecall

@[expose] public section

/- Lemma 13.20.2 says that the right-derived indexing diagram is essentially constant at every
object under enough injectives.  ReasLib retains this source-level meaning through
`Functor.RightDerived.DefinedAt`; Mathlib's weaker pointwise-existence instance remains available
as a canonical companion. -/

open CategoryTheory
open ComplexShape

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section Generic

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Category.{v₂} 𝒟] [Limits.HasZeroObject 𝒟]
  [HasShift 𝒟 ℤ] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] [IsTriangulated 𝒟]
  (F : HomotopyCategory.Plus 𝒜 ⥤ 𝒟)
  [F.CommShift ℤ] [F.IsTriangulated]

/- Lemma 13.20.2 (1): the right derived functor of an exact functor on `K⁺(𝒜)` is
source-defined everywhere. -/
@[stacks 05TI "(1)"] #check
  Functor.KInjective.Bounded.everywhereDefinedOfEnoughInjectives F

#check (inferInstance :
  F.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso 𝒜))

end Generic

section Additive

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [EnoughInjectives 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- Lemma 13.20.2 (2): the bounded-below right derived functor of an additive functor is
source-defined everywhere. -/
@[stacks 05TI "(2)"] #check
  Functor.KInjective.Bounded.everywhereDefinedOfEnoughInjectives
    F.toBoundedBelowDerived

#check (inferInstance :
  F.toBoundedBelowDerived.HasPointwiseRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso 𝒜))

end Additive

/- Companion construction: every bounded-below complex admits a quasi-isomorphism to an
injective complex. -/
@[stacks 05TI] #check @HomotopyCategory.Plus.Injective.exists_quasiIso

end CategoryTheory
