module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.OpenSubsetExtensionByInitial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubsetExtensionByInitial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u v

/-
The project dependency provides the concrete presheaf, sheaf, and module-valued extension
functors. The abelian clauses are their `AddCommGrpCat` specializations, while the general and
module clauses use those owners directly. Keeping this item as tagged recalls avoids a second
wrapper layer and exposes the same functors reused by the subsequent section results.
-/

section

variable {X : TopCat.{u}}

section AbelianExtensionByZero

variable (U : Opens X)

/- Definition 6.31.5 (1), source-facing specialization: for an abelian presheaf `ℱ` on `U`,
extension by zero is the `AddCommGrpCat` specialization `jₚ! U` of the canonical presheaf owner
`TopCat.Presheaf.ExtensionByInitial.functor`. -/
@[stacks 00A4 "abelian presheaf extension by zero"]
#check
  (jₚ! U :
    (TopCat.Opens.Subspace.space U).Presheaf AddCommGrpCat.{u} ⥤ X.Presheaf AddCommGrpCat.{u})

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Definition 6.31.5 (2), source-facing specialization: for an abelian sheaf `ℱ` on `U`,
extension by zero is the `AddCommGrpCat` specialization `j! U` of the canonical sheaf owner
`TopCat.Sheaf.ExtensionByInitial.functor`. -/
@[stacks 00A4 "abelian sheaf extension by zero"]
#check
  (j! U :
    (TopCat.Opens.Subspace.space U).Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u})

end AbelianExtensionByZero

section PresheafExtensionByInitial

variable {C : Type v} [Category.{v} C] [HasInitial C]
variable (U : Opens X)

/- Definition 6.31.5 (3): for a category `C` with an initial object, extension by the initial
object along `U ↪ X` is the canonical presheaf functor
`TopCat.Presheaf.ExtensionByInitial.functor U`. -/
@[stacks 00A4 "presheaf extension by the initial object"]
recall TopCat.Presheaf.ExtensionByInitial.functor

end PresheafExtensionByInitial

section SheafExtensionByInitial

variable {C : Type v} [Category.{v} C] [HasInitial C]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]
variable (U : Opens X)

/- Definition 6.31.5 (4): for sheaves valued in a category with an initial object and
sheafification, extension by the initial object along `U ↪ X` is the canonical sheaf functor
`TopCat.Sheaf.ExtensionByInitial.functor U`. -/
@[stacks 00A4 "sheaf extension by the initial object"]
recall TopCat.Sheaf.ExtensionByInitial.functor

end SheafExtensionByInitial

section ModulePresheafExtensionByZero

variable (U : Opens X)
variable (𝒪 : X.Presheaf CommRingCat.{u})

/- The generic owner also supports modules over possibly noncommutative ring presheaves. -/
recall PresheafOfModules.OpenSubset.ExtensionByZero.functorOfPullback

/- Definition 6.31.5 (5): under the Stacks convention that rings are commutative with `1`,
extension by zero sends presheaves of `𝒪|_U`-modules to presheaves of `𝒪`-modules. -/
@[stacks 00A4 "presheaf of modules extension by zero"]
#check
  ((PresheafOfModules.OpenSubset.ExtensionByZero.functorOfPullback U
      (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪)) :
    PresheafOfModules
        ((Presheaf.pullback RingCat.{u} (TopCat.Opens.Subspace.inclusion U)).obj
          (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪)) ⥤
      PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪))

end ModulePresheafExtensionByZero

section ModuleSheafExtensionByZero

variable (U : Opens X)
variable (𝒪 : X.Sheaf CommRingCat.{u})

/- The generic owner also supports modules over possibly noncommutative ring sheaves. -/
recall SheafOfModules.OpenSubset.ExtensionByZero.functor

/- Definition 6.31.5 (6): under the Stacks convention that rings are commutative with `1`,
extension by zero sends sheaves of `𝒪|_U`-modules to sheaves of `𝒪`-modules. -/
@[stacks 00A4 "sheaf of modules extension by zero"]
#check
  ((SheafOfModules.OpenSubset.ExtensionByZero.functor U
      (TopCat.Sheaf.ringSheafOfComm 𝒪)) :
    SheafOfModules
        ((Sheaf.pullback RingCat.{u} (TopCat.Opens.Subspace.inclusion U)).obj
          (TopCat.Sheaf.ringSheafOfComm 𝒪)) ⥤
      SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪))

end ModuleSheafExtensionByZero

end
