module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Basic

/-!
# Exact enriched Hom complexes from graded-injective targets

Precomposition against a graded-injective differential graded module sends every short exact
sequence of DG modules to a short exact sequence of enriched Hom complexes.  This is stronger
than the admissible-triangle formalism: the input short exact sequence need not split after
forgetting the differential.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.HomComplex

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 : DGA(𝒪)}

/-- The two contravariant enriched-Hom maps associated to a short complex compose to zero. -/
theorem precomp_comp_zero (S : ShortComplex Mod(𝒜, d)) (I : Mod(𝒜, d)) :
    DifferentialGradedCategory.HomComplex.precomp (Y := I) (homToCompHom S.g) ≫
      DifferentialGradedCategory.HomComplex.precomp (Y := I) (homToCompHom S.f) = 0 := sorry

/-- The contravariant enriched-Hom short complex associated to a DG-module short complex and a
fixed target. -/
@[stacks 0FSQ "contravariant Hom short complex"]
noncomputable def precompShortComplex
    (S : ShortComplex Mod(𝒜, d)) (I : Mod(𝒜, d)) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℤ) where
  X₁ := DifferentialGradedCategory.homComplex S.X₃ I
  X₂ := DifferentialGradedCategory.homComplex S.X₂ I
  X₃ := DifferentialGradedCategory.homComplex S.X₁ I
  f := DifferentialGradedCategory.HomComplex.precomp (Y := I) (homToCompHom S.g)
  g := DifferentialGradedCategory.HomComplex.precomp (Y := I) (homToCompHom S.f)
  zero := precomp_comp_zero S I

/-- A graded-injective target sends every short exact sequence of DG modules to a short exact
sequence of enriched Hom complexes. -/
@[stacks 0FSQ]
theorem precomp_shortExact (S : ShortComplex Mod(𝒜, d)) (hS : S.ShortExact)
    (I : Mod(𝒜, d)) [Module.IsKInjective.GradedInjective I] :
    (precompShortComplex S I).ShortExact := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.HomComplex
