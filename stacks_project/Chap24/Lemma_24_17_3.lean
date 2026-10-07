module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Bimodule.TensorHom
import StacksCheckRecall

/-!
# Lemma 24.17.3

The reusable tensor-Hom construction is owned by the generic `CategoryTheory.Bimod` API and its
ringed-site differential graded specialization.  No chapter-local choice of tensor product,
internal Hom, or closed structure is required.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedBimodule.TensorHom

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, d))
variable (N : Mod(𝒜, 𝒝, d)) (L : Mod(𝒝, d))

/- Lemma 24.17.3 (1) (0FRS): maps of right DG `𝒝`-modules from the balanced
tensor `M ⊗_𝒜 N` to `L` are naturally equivalent to maps of right DG `𝒜`-modules
from `M` to the relative internal Hom from `N` to `L`. -/
@[stacks 0FRS]
#check
  (homEquiv M N L :
    (tensor M N ⟶ L.toBimod) ≃ (M.toBimod ⟶ internalHom N L))

/- The Hom equivalence is the component of an adjunction of reusable functors. -/
#check adjunction N

/- Naturality of the Hom equivalence in `M`, `N`, and `L`. -/
#check @homEquiv_natural_source
#check @homEquiv_natural_bimodule
#check @homEquiv_natural_target

/- Lemma 24.17.3 (2) (0FRS): the DG internal-Hom complex from `M ⊗_𝒜 N`
to `L` is canonically isomorphic to the iterated internal-Hom complex. -/
@[stacks 0FRS "internal-Hom complex currying"]
#check
  (internalHomIso M N L :
    homComplex (tensor M N) L.toBimod ≅ homComplex M.toBimod (internalHom N L))

/- Naturality of the internal-Hom complex isomorphism in `M`, `N`, and `L`. -/
#check @internalHomIso_natural_source
#check @internalHomIso_natural_bimodule
#check @internalHomIso_natural_target

end


end SheafOfModules.RingedSite.DifferentialGradedBimodule.TensorHom

end
