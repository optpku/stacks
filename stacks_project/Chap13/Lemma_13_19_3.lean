module

import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import StacksCheckRecall

@[expose] public section

/- Lemma 13.19.3 is owned by the reusable cochain-complex projective-resolution
API.  Enough projectives supplies the object-level resolution instance, and
the two remaining statements are the bounded-above resolution bridges. -/

open CategoryTheory

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughProjectives 𝒜]

@[stacks 0646] #check (inferInstance : HasProjectiveResolutions 𝒜)

end

@[stacks 0646] #check
  @CochainComplex.ProjectiveResolution.nonempty_of_eventually_isZero_homology
@[stacks 0646] #check
  @CochainComplex.ProjectiveResolution.exists_strictlyLE_with_termwise_epi

end
