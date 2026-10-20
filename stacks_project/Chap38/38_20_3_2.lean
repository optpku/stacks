module

public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [AddCommGroup M] [Module B M]

/- 38.20.3.2: `F_lf` sends a local `A`-algebra `T` to a singleton when condition `05ML`
holds for the tensor-product base change, and to the empty set otherwise. -/
@[stacks 05MM] #check (LocalAlgCat.Flattening.functor A B M : LocalAlgCat.{v} A ⥤ Type u)

#check (LocalAlgCat.Flattening.functor_obj_nonempty_iff A B M :
  ∀ T : LocalAlgCat.{v} A,
    Nonempty ((LocalAlgCat.Flattening.functor A B M).obj T) ↔
      LocalAlgCat.Flattening.IsFlatAtClosedPoint A B M T)

#check (LocalAlgCat.Flattening.functor_obj_isEmpty_iff A B M :
  ∀ T : LocalAlgCat.{v} A,
    IsEmpty ((LocalAlgCat.Flattening.functor A B M).obj T) ↔
      ¬ LocalAlgCat.Flattening.IsFlatAtClosedPoint A B M T)

#check (LocalAlgCat.Flattening.functorObjSubsingleton A B M :
  ∀ T : LocalAlgCat.{v} A, Subsingleton ((LocalAlgCat.Flattening.functor A B M).obj T))
