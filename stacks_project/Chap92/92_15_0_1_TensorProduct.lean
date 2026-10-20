module

public import ReasLib.RingTheory.CotangentComplex.TensorProduct

open Algebra.CotangentComplex CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

#check (Algebra.CotangentComplex.tensorProductCone :
  ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B], DerivedCategory (ModuleCat.{u} (A ⊗[R] B)))

#check (Algebra.CotangentComplex.sumMap :
  ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B],
    DerivedCategory.Q.obj (tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B) ⟶
      derived R (A ⊗[R] B))
