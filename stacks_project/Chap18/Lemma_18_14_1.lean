/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v})
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Lemma 18.14.1 (03DA) (1): sheaves of 𝒪-modules form an abelian category. -/
@[stacks 03DA "abelian category"]
#check (inferInstance : Abelian (SheafOfModules.{max u v} 𝒪))

/- Lemma 18.14.1 (03DA) (2): the forgetful functor to additive sheaves is exact. -/
@[stacks 03DA "exact forgetful functor"]
#check (SheafOfModules.toSheaf_exact 𝒪 :
  exactFunctor (SheafOfModules.{max u v} 𝒪)
    (Sheaf J AddCommGrpCat.{max u v}) (SheafOfModules.toSheaf.{max u v} 𝒪))

/- Exactness of a short complex is therefore detected after forgetting the module structure. -/
variable (S : ShortComplex (SheafOfModules.{max u v} 𝒪)) in
#check (S.exact_map_iff_of_faithful (SheafOfModules.toSheaf.{max u v} 𝒪)).symm

#check PreservesKernel.iso (SheafOfModules.toSheaf.{max u v} 𝒪)
#check PreservesCokernel.iso (SheafOfModules.toSheaf.{max u v} 𝒪)
