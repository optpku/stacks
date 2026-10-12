/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.3 is owned by the reusable cochain-complex injective-resolution
API.  Enough injectives supplies the object-level resolution instance, and the
two remaining statements are the bounded-below resolution bridges. -/

open CategoryTheory

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

@[stacks 013K] #check (inferInstance : HasInjectiveResolutions 𝒜)

end

@[stacks 013K] #check
  @CochainComplex.InjectiveResolution.nonempty_of_eventually_isZero_homology
@[stacks 013K] #check
  @CochainComplex.InjectiveResolution.exists_strictlyGE_with_termwise_mono

end
