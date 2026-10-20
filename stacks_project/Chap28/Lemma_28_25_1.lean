module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Sections
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

/- Lemma 28.25.1 (1): the canonical comparison from the ideal-power Hom colimit to sections on
the ideal complement is injective. -/
@[stacks 01PM] #check
  (AlgebraicGeometry.Scheme.Modules.idealPowerHomColimitToComplementSections_injective :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat A),
      Function.Injective
        (AlgebraicGeometry.Scheme.Modules.idealPowerHomColimitToComplementSections
          I hI M).hom)

/- Lemma 28.25.1 (2): under the elementwise annihilator condition, the canonical comparison from
the ideal-power Hom colimit to sections on the ideal complement is an isomorphism. -/
@[stacks 01PM] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_idealPowerHomColimitToComplementSections_of_annihilatorCondition :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat A),
      (∀ x : M, (∀ a : A, a ∈ I → a • x = 0) → x = 0) →
        IsIso (AlgebraicGeometry.Scheme.Modules.idealPowerHomColimitToComplementSections
          I hI M))

/- Lemma 28.25.1 (3): for the quotients by the corresponding ideal-power annihilated
submodules, the canonical Hom-colimit comparison is an isomorphism. -/
@[stacks 01PM] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_idealPowerQuotientHomColimitToComplementSections :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat A),
      IsIso (AlgebraicGeometry.Scheme.Modules.idealPowerQuotientHomColimitToComplementSections
        I hI M))

end AlgebraicGeometry.Scheme.Modules
