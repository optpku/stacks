module

public import stacks_project.Chap90.Definition_90_11_1_ModuleLinear
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable (Lfg : FGModuleCat.{v} R ⥤ ModuleCat.{v} R)
variable (L : ModuleCat.{v} R ⥤ ModuleCat.{v} R)

/- Definition 90.11.1: a functor `L : FGModuleCat R ⥤ ModuleCat R`, resp.
`L : ModuleCat R ⥤ ModuleCat R`, is R-linear if for every pair of objects `M, N`
the induced map `L.map : (M ⟶ N) → (L.obj M ⟶ L.obj N)` is an R-module homomorphism.
This is owned by `Functor.ModuleLinear`; the Hom-module map is `Functor.mapLinearMap`. -/
@[stacks 06I3] #check @CategoryTheory.Functor.ModuleLinear

#check @CategoryTheory.Functor.mapLinearMap

#check Functor.ModuleLinear R Lfg

#check Functor.ModuleLinear R L
