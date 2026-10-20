/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe w u

variable {X : TopCat.{w}}
variable [UnivLE.{w, u}]

/- Mathlib's `SheafOfModules 𝒪` and `SheafOfModules.Hom` are the exact canonical owners for the
source objects and morphisms. The neutral `ModuleSheaf` support owns the underlying-ring
specialization, same-space change-of-scalars maps, stalk module instance, and notation `Mod(𝒪)`,
so later consumers need not depend on this numbered recall file. -/

/- The generic mathlib owner also supports sheaves of modules over possibly noncommutative ring
sheaves. -/
recall SheafOfModules

/- Its morphism owner is the morphism type of the underlying presheaves of modules. -/
recall SheafOfModules.Hom

variable (𝒪 : X.Sheaf CommRingCat.{u})

/- Definition 6.10.1 (1): under the Stacks convention that rings are commutative with `1`, a
sheaf of `𝒪`-modules is an object of the canonical mathlib owner over the underlying
`RingCat`-valued sheaf. -/
@[stacks 0077 "sheaves of modules over a sheaf of rings"]
#check SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)

variable
  (ℱ 𝒢 : Mod(TopCat.Sheaf.ringSheafOfComm 𝒪))

/- Definition 6.10.1 (2): a morphism of sheaves of `𝒪`-modules is represented by the canonical
`SheafOfModules.Hom` owner. -/
@[stacks 0077 "morphisms of sheaves of modules"]
#check SheafOfModules.Hom ℱ 𝒢

/- Definition 6.10.1 (3): the source notation `Hom_𝒪(ℱ, 𝒢)` is the categorical hom-type in the
canonical module-sheaf category. -/
@[stacks 0077 "morphisms of sheaves of modules"]
#check (ℱ ⟶ 𝒢)

/- Definition 6.10.1 (4): the category of sheaves of `𝒪`-modules is denoted `Mod(𝒪)`. -/
@[stacks 0077 "category of sheaves of modules"]
#check Mod(TopCat.Sheaf.ringSheafOfComm 𝒪)

/- Companion recall: the underlying presheaf of `𝒪`-modules of a sheaf of `𝒪`-modules is
obtained by the canonical forgetful functor `SheafOfModules.forget`. -/
#check (SheafOfModules.forget (TopCat.Sheaf.ringSheafOfComm 𝒪))

/- Companion recall: the underlying sheaf of abelian groups of a sheaf of `𝒪`-modules is
obtained by the canonical functor `SheafOfModules.toSheaf`. -/
#check (SheafOfModules.toSheaf (TopCat.Sheaf.ringSheafOfComm 𝒪))
