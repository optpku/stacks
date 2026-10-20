module

public import ReasLib.Algebra.Homology.DerivedCategory.Koszul.Family
public import ReasLib.RingTheory.Sequence.Regularity.ClosedFiber
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension

@[expose] public section

noncomputable section

open CategoryTheory
open IsLocalRing
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v

namespace CategoryTheory.DerivedCategory

/-- A perfect derived object with closed-fiber Koszul form lifts to a Koszul complex on a regular
sequence whose quotient is flat over the base ring. -/
theorem exists_koszul_lift_of_closedFiber
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [IsLocalRing R] [IsLocalRing A]
    [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    (hess : RingHom.EssFinitePresentation (algebraMap R A))
    {r : ℕ}
    (fbar : Fin r → Ideal.Fiber (maximalIdeal R) A)
    (hfbar_mem : ∀ i,
      fbar i ∈ Ideal.map (algebraMap A (Ideal.Fiber (maximalIdeal R) A)) (maximalIdeal A))
    (hfbar_reg : RingTheory.Sequence.IsRegular
      (Ideal.Fiber (maximalIdeal R) A) (List.ofFn fbar))
    (K : DerivedCategory (ModuleCat A))
    (hK_perfect : K.IsPerfect)
    (hK_fiber : IsIsomorphic
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (Ideal.Fiber (maximalIdeal R) A))).obj K)
      (KoszulComplex.derivedFamily fbar)) :
    ∃ f : Fin r → A,
      (∀ i, algebraMap A (Ideal.Fiber (maximalIdeal R) A) (f i) = fbar i) ∧
      RingTheory.Sequence.IsRegular A (List.ofFn f) ∧
      IsIsomorphic K (KoszulComplex.derivedFamily f) ∧
      Module.Flat R (A ⧸ Ideal.span (Set.range f)) := sorry

end CategoryTheory.DerivedCategory
