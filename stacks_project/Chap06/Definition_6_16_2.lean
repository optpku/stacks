/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Types.Morphisms
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v

variable {X : TopCat.{u}}

/- Definition 6.16.2 (1): a subpresheaf of a set-valued presheaf is the canonical
`CategoryTheory.Subfunctor`, whose objectwise subsets are preserved by restriction maps. -/
@[stacks 007U "subpresheaves as restriction-stable objectwise subsets"]
recall CategoryTheory.Subfunctor

section

variable {ℱ : X.Sheaf (Type v)}
variable (𝒢 : CategoryTheory.Subfunctor ℱ.presheaf)

/- Definition 6.16.2 (2): a subpresheaf of a sheaf is a subsheaf when the subpresheaf itself
satisfies the sheaf condition. -/
@[stacks 007U "subsheaves as subfunctors satisfying the sheaf condition"]
#check Presieve.IsSheaf (Opens.grothendieckTopology X) 𝒢.toFunctor

end

/- Definition 6.16.2 (3): injective morphisms of presheaves of sets are owned by the categorical
`Mono` predicate; `NatTrans.mono_iff_mono_app` and `CategoryTheory.mono_iff_injective` give the
sectionwise view. -/
@[stacks 007U "injective morphisms of presheaves of sets"]
#check NatTrans.mono_iff_mono_app
#check CategoryTheory.mono_iff_injective

/- Definition 6.16.2 (4): surjective morphisms of presheaves of sets are owned by `Epi`; the
sectionwise view is given by `NatTrans.epi_iff_epi_app` and `CategoryTheory.epi_iff_surjective`. -/
@[stacks 007U "surjective morphisms of presheaves of sets"]
#check NatTrans.epi_iff_epi_app
#check CategoryTheory.epi_iff_surjective

/- Definition 6.16.2 (5): injective morphisms of sheaves of sets are likewise owned by `Mono`;
the sectionwise view is obtained from `Sheaf.Hom.mono_iff_presheaf_mono` and the same functor
category criteria. -/
@[stacks 007U "injective morphisms of sheaves of sets"]
#check Sheaf.Hom.mono_iff_presheaf_mono

section

variable {ℱ 𝒢 : X.Sheaf (Type v)} (φ : ℱ ⟶ 𝒢)

/- Definition 6.16.2 (6): a morphism of sheaves of sets is surjective precisely when sections
admit local preimages, as expressed by the canonical site-theoretic predicate. -/
@[stacks 007U "locally surjective morphisms of sheaves of sets"]
#check
  (CategoryTheory.Sheaf.IsLocallySurjective
    (J := Opens.grothendieckTopology X) φ)

end
