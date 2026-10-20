module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.Preadditive

/-!
# Limits of graded module sheaves

This leaf owns the pointwise completeness, cocompleteness, abelian, and AB5 infrastructure for
graded module sheaves. It also records that both the underlying graded-object functor and every
degree evaluation preserve the corresponding constructions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedModuleSheaf

section Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- Lemma 24.4.2 (0FR0): graded module sheaves have all small limits. -/
@[stacks 0FR0 "limits"]
instance instHasLimits (𝒜 : GradedAlgebraSheaf 𝒪 ι) : HasLimits (Mod(𝒜)) := sorry

/-- The underlying graded-object functor preserves all small limits. -/
instance forgetToGradedPreservesLimits (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    PreservesLimits (forgetToGraded 𝒜) := sorry

/-- Lemma 24.4.2 (0FR0): evaluation in every degree preserves all small limits. -/
@[stacks 0FR0 "degree evaluation preserves limits"]
instance evalPreservesLimits (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) :
    PreservesLimits (eval 𝒜 n) := sorry

end Limits

section Colimits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- Lemma 24.4.2 (0FR0): graded module sheaves have all small colimits. -/
@[stacks 0FR0 "colimits"]
instance instHasColimits
    [h_sheafify : HasWeakSheafify J AddCommGrpCat.{max u v}]
    [h_local : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒜 : GradedAlgebraSheaf 𝒪 ι) : HasColimits (Mod(𝒜)) := sorry

/-- The underlying graded-object functor preserves all small colimits. -/
instance forgetToGradedPreservesColimits
    [h_sheafify : HasWeakSheafify J AddCommGrpCat.{max u v}]
    [h_local : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    PreservesColimits (forgetToGraded 𝒜) := sorry

/-- Lemma 24.4.2 (0FR0): evaluation in every degree preserves all small colimits. -/
@[stacks 0FR0 "degree evaluation preserves colimits"]
instance evalPreservesColimits
    [h_sheafify : HasWeakSheafify J AddCommGrpCat.{max u v}]
    [h_local : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) :
    PreservesColimits (eval 𝒜 n) := sorry

end Colimits

section Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- Lemma 24.4.2 (0FR0): graded module sheaves form an abelian category with the
canonical degreewise preadditive structure. -/
@[stacks 0FR0 "abelian category"]
instance instAbelian
    [h_sheafify : HasSheafify J AddCommGrpCat.{max u v}]
    [h_local : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒜 : GradedAlgebraSheaf 𝒪 ι) : Abelian (Mod(𝒜)) where
  toPreadditive := instPreadditive 𝒜
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- Lemma 24.4.2 (0FR0): filtered colimits of graded module sheaves are exact. -/
@[stacks 0FR0 "AB5"]
instance instAB5
    [h_sheafify : HasSheafify J AddCommGrpCat.{max u v}]
    [h_local : J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒜 : GradedAlgebraSheaf 𝒪 ι) : AB5 (Mod(𝒜)) := sorry

end Abelian

end SheafOfModules.RingedSite.GradedModuleSheaf
