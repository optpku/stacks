module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w u

variable {X : TopCat.{w}}

/-
Mathlib's `PresheafOfModules 𝒪` is the canonical data owner: its objects package the
`𝒪(U)`-modules and semilinear restriction maps, while `PresheafOfModules.Hom` packages the
objectwise linear maps satisfying the source commutative square. The neutral `ModulePresheaf`
support owns the underlying-ring specialization and the notation `PMod(𝒪)`, so later consumers
need not import this numbered recall file.
-/

/- The generic mathlib owner also supports presheaves of modules over possibly noncommutative
rings. -/
recall PresheafOfModules

/- Its morphism owner packages the objectwise linear maps compatible with restriction. -/
recall PresheafOfModules.Hom

variable (𝒪 : X.Presheaf CommRingCat.{u})

/- Definition 6.6.1 (1): under the Stacks convention that rings are commutative with `1`, a
presheaf of `𝒪`-modules is an object of the canonical mathlib owner over the underlying
`RingCat`-valued presheaf. -/
@[stacks 006Q "presheaves of modules over a presheaf of rings"]
#check PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪)

variable
  (ℱ 𝒢 : PMod(CategoryTheory.Presheaf.ringPresheafOfComm 𝒪))

/- Definition 6.6.1 (2): a morphism of presheaves of `𝒪`-modules is represented by the canonical
`PresheafOfModules.Hom` owner. -/
@[stacks 006Q "morphisms of presheaves of modules"]
#check PresheafOfModules.Hom ℱ 𝒢

/- Definition 6.6.1 (3): the source notation `Hom_𝒪(ℱ, 𝒢)` is the categorical hom-type in the
canonical module-presheaf category. -/
@[stacks 006Q "morphisms of presheaves of modules"]
#check (ℱ ⟶ 𝒢)

/- Definition 6.6.1 (4): the category of presheaves of `𝒪`-modules is denoted `PMod(𝒪)`. -/
@[stacks 006Q "category of presheaves of modules"]
#check PMod(CategoryTheory.Presheaf.ringPresheafOfComm 𝒪)
