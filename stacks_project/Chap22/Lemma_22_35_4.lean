/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Hom.Cohomology
import StacksCheckRecall

@[expose] public section

noncomputable section

universe r u v w z g

open CategoryTheory DifferentialGradedCategory
open SheafOfModules.CommAlg
open SheafOfModules.CommAlg.TensorWithObject
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}
variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

variable (K : Complex.{r, u, v, w, max u z} O)
variable (M N : DifferentialGradedModule.Derived.Category (endDGA K))
variable (n : ℤ)

/- Lemma 22.35.4 (0CS6) (1): derived tensoring with `K` induces the canonical natural
transformation from derived Hom over `endDGA K` to derived `RHom` of `O`-modules after
tensoring both variables with `K`. -/
@[stacks 0CS6 "derived tensor-Hom comparison"] #check
  SheafOfModules.CommAlg.TensorWithObject.Derived.Hom.comparison K

section Cohomology

variable [IsGrothendieckAbelian.{g}
  (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)]

/- Lemma 22.35.4 (0CS6) (2): on degree-`n` cohomology, this comparison is the map on shifted
Homs induced by the derived tensor functor. -/
@[stacks 0CS6 "cohomology of the derived tensor-Hom comparison"] #check
  SheafOfModules.CommAlg.TensorWithObject.Derived.Hom.Cohomology.cohomologyMap_shiftedHom K M N n

end Cohomology

/- The objectwise morphism is the component of the comparison in both derived variables. -/
#check Derived.Hom.comparisonApp K M N

section PropertyP

variable (P Q : Modules K)
variable (hP : DifferentialGradedModule.HasPropertyP (endDGA K) P)
variable (hQ : DifferentialGradedModule.HasPropertyP (endDGA K) Q)

/- On property-(P) representatives, the abstract morphism is computed by the strict enriched
Hom map followed by the global derived-Hom unit. -/
#check Derived.Hom.comparison_fac K
#check Derived.Hom.comparison_app_propertyP K P Q hP hQ

end PropertyP

/- The abstract 0CS6 target is global `RHom` after applying derived tensor in both variables;
it is distinct from the simultaneous right derivation of `Hom(F(-), F(-))`. -/
#check Derived.Hom.Source.functor K
#check Derived.Hom.Target.functor K

/- The reusable degreewise comparison is exposed by the dedicated cohomology leaf. -/
#check Derived.Hom.Cohomology.sourceFunctor K
#check Derived.Hom.Cohomology.targetFunctor K
#check Derived.Hom.Cohomology.comparison K n
#check Derived.Hom.Cohomology.cohomologyMap K M N n
#check Derived.Hom.Cohomology.sourceLinearEquiv K M N n

section TargetRepresentability

variable [IsGrothendieckAbelian.{g}
  (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)]

#check Derived.Hom.Cohomology.targetLinearEquiv K M N n

end TargetRepresentability
