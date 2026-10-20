/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Ext.Single
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open scoped DerivedExt

universe w' w v u

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜]
variable (X Y : DerivedCategory 𝒜) (i : ℤ)

/- Definition 13.27.1 (Stacks 06XQ): `Ext⁽i⁾(X, Y)` is the shifted morphism group
`ShiftedHom X Y i` in the derived category. -/
@[stacks 06XQ] #check Ext⁽i⁾(X, Y)
#check @ShiftedHom
#check @DerivedCategory.singleFunctor

end

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜]
  [HasExt.{w} 𝒜] (A B : 𝒜) (n : ℕ)

#check (Ext A B n)
#check @Ext.homEquiv
#check @Ext.homAddEquiv
#check @Ext.homAddEquiv_comp_mk₀
#check @Ext.homAddEquiv_mk₀_comp

end
