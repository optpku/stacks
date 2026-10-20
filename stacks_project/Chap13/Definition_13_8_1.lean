/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Bounded
import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

universe v u
variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

-- Definition 13.8.1: the categories of bounded-above / bounded cochain complexes, and the
-- corresponding bounded homotopy categories, now live in the shared library.
@[stacks 013H] #check @CochainComplex.minus
#check @CochainComplex.minus_iff
#check @CochainComplex.Minus
#check @CochainComplex.bounded
#check @CochainComplex.bounded_iff
#check @CochainComplex.Bounded

#check @HomotopyCategory.plus
#check @HomotopyCategory.plus_quotient_obj_iff
#check @HomotopyCategory.Plus
#check @HomotopyCategory.minus
#check @HomotopyCategory.minus_iff
#check @HomotopyCategory.Minus
#check @HomotopyCategory.bounded
#check @HomotopyCategory.bounded_iff
#check @HomotopyCategory.Bounded

#check @HomotopyCategory.Plus.quotient
#check @HomotopyCategory.Minus.quotient
#check @HomotopyCategory.Bounded.quotient

#check (Comp(𝒜))
#check (Comp⁺(𝒜))
#check (Comp⁻(𝒜))
#check (Compᵇ(𝒜))
#check (K(𝒜))
#check (K⁺(𝒜))
#check (K⁻(𝒜))
#check (Kᵇ(𝒜))
