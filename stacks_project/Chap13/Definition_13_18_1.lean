/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

universe v u
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

-- Definition 13.18.1: a bounded-below injective resolution of a cochain complex is a
-- quasi-isomorphism from the given complex to a bounded-below cochain complex of injective
-- objects. Now lives in the shared library.
@[stacks 013I] #check @CochainComplex.InjectivePlus
@[stacks 013I] #check @CochainComplex.Plus.TermsIn
@[stacks 013I] #check @CochainComplex.Plus.TermsIn.instIsKInjective
@[stacks 013I] #check @CochainComplex.InjectiveResolution
@[stacks 013I] #check @CochainComplex.InjectiveResolution.plus
@[stacks 013I] #check @CochainComplex.InjectiveResolution.exists_isStrictlyGE
@[stacks 013I] #check @CochainComplex.InjectiveResolution.injective
@[stacks 013I] #check @CochainComplex.InjectiveResolution.instIsKInjective
