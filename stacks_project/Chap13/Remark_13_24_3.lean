module

import Mathlib.Algebra.Category.ModuleCat.AB
import ReasLib.Algebra.Category.ModuleCat.Presheaf.Grothendieck
import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Functorial
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.24.3

The listed module categories are examples of the shared Grothendieck-abelian and functorial
injective-embedding infrastructure. This file records only their Chapter 13 consequence.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open scoped AlgebraicGeometry

universe v u

section RingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u})

/- Ringed-space module sheaves inherit the Grothendieck-abelian owner and hence functorial
injective embeddings. -/
#synth HasFunctorialInjectives X.Modules

/- Remark 13.24.3 (Stacks 0142): bounded-below complexes of modules on a ringed space have a
strict functorial injective resolution. -/
@[stacks 0142] #check
  (CochainComplex.FunctorialInjectiveResolution.nonempty :
    Nonempty (CochainComplex.FunctorialInjectiveResolution X.Modules))

end RingedSpace

section RingedSite

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (𝒪 : Sheaf J RingCat.{max u v})

/- The ringed-site hypothesis supplies the sheafification data needed by the shared
Grothendieck-abelian owner. -/
#synth HasFunctorialInjectives (SheafOfModules.{max u v} 𝒪)

#check
  (CochainComplex.FunctorialInjectiveResolution.nonempty :
    Nonempty (CochainComplex.FunctorialInjectiveResolution
      (SheafOfModules.{max u v} 𝒪)))

end RingedSite

section ModuleCat

variable (R : Type u) [Ring R]

/- Mathlib's `ModuleCat.AB` is the canonical Grothendieck-abelian owner for modules over a
ring. -/
#synth HasFunctorialInjectives (ModuleCat R)

#check
  (CochainComplex.FunctorialInjectiveResolution.nonempty :
    Nonempty (CochainComplex.FunctorialInjectiveResolution (ModuleCat R)))

end ModuleCat

section PresheafOfModules

variable {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v})

/- Presheaves of modules use the neutral presheaf Grothendieck owner, not a chapter-local
separator construction. -/
#synth HasFunctorialInjectives (PresheafOfModules.{max u v} 𝒪)

#check
  (CochainComplex.FunctorialInjectiveResolution.nonempty :
    Nonempty (CochainComplex.FunctorialInjectiveResolution
      (PresheafOfModules.{max u v} 𝒪)))

end PresheafOfModules
