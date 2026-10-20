module

public import ReasLib.Algebra.Category.ModuleCat.LinearLift

/-!
# The unique `R`-linear lift of a finite-product-preserving functor to types

A functor `L : C ⥤ Type v` from an `R`-linear category with finite products and a
zero object, with `L.obj 0` a singleton and `L` preserving finite products, lifts
uniquely to an `R`-linear functor `C ⥤ ModuleCat R` whose composite with the
forgetful functor is `L`.
-/

@[expose] public section

open CategoryTheory hiding Linear
open Limits ZeroObject

noncomputable section

universe u v w

namespace CategoryTheory.Functor

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasBinaryProducts C]

/- The sum map `M ⨯ M ⟶ M` remains available through the shared owner. -/
#check (CategoryTheory.Functor.sumHom : ∀ (M : C), M ⨯ M ⟶ M)

/- The sum map is the sum of the binary product projections. -/
#check (CategoryTheory.Functor.sumHom_eq :
  ∀ (M : C), sumHom M = prod.fst + prod.snd)

variable {R : Type u} [CommRing R]
variable [CategoryTheory.Linear R C] [HasFiniteProducts C] [HasZeroObject C]
variable (L : C ⥤ Type v) [PreservesFiniteProducts L] [Unique (L.obj 0)]

/- The concrete lift is available through the shared owner. -/
#check (CategoryTheory.Functor.linearLift L : C ⥤ ModuleCat.{v} R)

/- The lift has exactly the original underlying set-valued functor. -/
#check (CategoryTheory.Functor.linearLift_comp_forget (R := R) L :
  linearLift L ⋙ forget (ModuleCat.{v} R) = L)

/- The lift is module-linear over `R`. -/
#check (CategoryTheory.Functor.instModuleLinear L :
  ModuleLinear R (linearLift L : C ⥤ ModuleCat.{v} R))

/- A module-linear functor with underlying functor `L` equals the concrete lift. -/
#check (CategoryTheory.Functor.linearLift_unique (R := R) L :
  ∀ (G : C ⥤ ModuleCat.{v} R), ∀ [ModuleLinear R G],
    G ⋙ forget (ModuleCat.{v} R) = L → G = linearLift L)

end CategoryTheory.Functor
