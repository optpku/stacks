module

public import stacks_project.Chap70.Lemma_70_14_5_SectionsWithSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X U : AlgebraicSpace S}
variable (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules)
variable (W : smallEtaleSite X)

/- The sheaf of sections supported in the closed complement of an open
subspace is the kernel of restriction along the open immersion. -/
@[stacks 0859]
#check (sectionsWithSupportIn ι F : X.Modules)

/- The canonical map to the original module sheaf is the kernel inclusion. -/
@[stacks 0859]
#check (sectionsWithSupportInι ι F : sectionsWithSupportIn ι F ⟶ F)

/- A section over an étale object lies in the kernel sheaf if and only if it is sent to zero
by the unit of `ι^* ⊣ ι_*`. -/
@[stacks 0859]
#check (mem_range_sectionsWithSupportInι_app_iff ι F W)

/- Lemma 70.14.5 (1): if `U ⟶ X` is quasi-compact, every affine étale `W` admits a finitely
generated ideal cutting out the preimage of the closed complement of `|U|`. -/
@[stacks 0859]
#check exists_fg_ideal_of_quasiCompact_openComplement

/- Lemma 70.14.5 (2): on such an affine étale `W`, the supported sections are the sections
annihilated by some power of that ideal. -/
@[stacks 0859]
#check range_sectionsWithSupportInι_app_eq_affine_idealPowerTorsion

/- Lemma 70.14.5 (3): under the same quasi-compactness hypothesis, the sheaf of supported
sections of a quasi-coherent module is quasi-coherent. -/
@[stacks 0859]
#check sectionsWithSupportIn_isQuasicoherent

end AlgebraicGeometry.AlgebraicSpace.Modules
