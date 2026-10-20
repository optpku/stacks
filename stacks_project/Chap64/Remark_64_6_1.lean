/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Triangulated
import ReasLib.Algebra.Homology.DerivedCategory.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe w v u

variable (𝒜 : Type u) [Category.{v} 𝒜]

section
variable [Abelian 𝒜]

#check (HasDerivedCategory.standard 𝒜 : HasDerivedCategory.{max u v} 𝒜)

/- Remark 64.6.1: there are some set-theoretical problems when 𝒜 is somewhat
arbitrary, which we will happily disregard. The standard localization has
morphisms in universe max u v; a chosen localization in universe w is expressed
by HasDerivedCategory.{w} 𝒜. The homotopy category K(𝒜) and the derived
category D(𝒜) are endowed with the structure of a triangulated category, and
the categories Comp(𝒜) and K(𝒜) can also be defined when 𝒜 is additive. -/
@[stacks 03T4] #check (HomotopyCategory.isTriangulated 𝒜 :
  IsTriangulated (HomotopyCategory 𝒜 (ComplexShape.up ℤ)))

variable [HasDerivedCategory.{w} 𝒜]

/- The derived category D(𝒜) is endowed with the structure of a triangulated
category. -/
@[stacks 03T4] #check (DerivedCategory.isTriangulated 𝒜 :
  IsTriangulated (DerivedCategory 𝒜))

end

section
variable [Preadditive 𝒜]

/- For a preadditive category, the complex and homotopy-category carriers and
their canonical category structures are available. -/
#check (CochainComplex 𝒜 ℤ : Type (max u v))
#check (HomotopyCategory 𝒜 (ComplexShape.up ℤ) : Type (max u v))
#check (inferInstance : Category (CochainComplex 𝒜 ℤ))
#check (inferInstance : Category (HomotopyCategory 𝒜 (ComplexShape.up ℤ)))

end
