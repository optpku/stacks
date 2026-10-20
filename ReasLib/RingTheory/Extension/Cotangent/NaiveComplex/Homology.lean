module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived

/-! # Homology maps of derived scalar extensions of naive cotangent morphisms -/

@[expose] public section

open CategoryTheory DerivedCategory

noncomputable section

universe u

namespace Algebra.NaiveCotangent

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
variable {k : Type u} [Field k] [Algebra A k]

/-- The degree-`i` homology map of derived scalar extension of `ξ` along
`A → k`. -/
def homologyMap {E : Minus (ModuleCat.{u} A)}
    (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A) (i : ℤ) :
    (homologyFunctor (ModuleCat k) i).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).obj
        (Minus.ι.obj E)) ⟶
    (homologyFunctor (ModuleCat k) i).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).obj
        (naiveCotangentObject Λ A)) :=
  (homologyFunctor (ModuleCat k) i).map
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).map ξ)

/-- `homologyMap ξ i` is the homology functor applied to derived extension of
scalars of `ξ`. -/
theorem homologyMap_eq {E : Minus (ModuleCat.{u} A)}
    (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A) (i : ℤ) :
    homologyMap ξ i =
      (homologyFunctor (ModuleCat k) i).map
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).map ξ) :=
  sorry

end Algebra.NaiveCotangent
