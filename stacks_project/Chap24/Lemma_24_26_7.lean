/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.KInjective
import StacksCheckRecall

/-!
# Lemma 24.26.7

A quasi-isomorphism into a K-injective replacement computes derived morphisms from intrinsic
homotopy classes.  The ReasLib theorem is stated at the minimal K-injective level, so it also
applies to graded-injective K-injective replacements.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} {𝒜 : DGA(𝒪)}
variable {M N I : Mod(𝒜, d)} (i : N ⟶ I) (hi : Module.quasiIso 𝒜 i)
variable [Module.IsKInjective.GradedInjective I]

/- Lemma 24.26.7 (0FT8): a graded-injective K-injective replacement computes all represented
derived morphisms. -/
@[stacks 0FT8]
#check
  (DerivedCategory.KInjective.homToDerivedRep_bijective (M := M) 𝒜 i hi :
    Function.Bijective
      (DerivedCategory.KInjective.homToDerivedRep 𝒜 i hi :
        ((toK 𝒜).obj M ⟶ (toK 𝒜).obj I) →
          ((DerivedCategory.Q 𝒜).obj M ⟶ (DerivedCategory.Q 𝒜).obj N)))

end SheafOfModules.RingedSite.DifferentialGradedModule
