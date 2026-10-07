module

public import ReasLib.Algebra.Category.CommAlgCat.Local

@[expose] public section

universe u v

#check (LocalAlgCat.of :
  ∀ (A : Type u) [CommRing A] (T : Type v) [CommRing T] [Algebra A T]
    [IsLocalRing T] [IsLocalHom (algebraMap A T)], LocalAlgCat.{v} A)
