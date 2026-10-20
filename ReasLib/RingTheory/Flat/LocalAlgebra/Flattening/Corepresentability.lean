module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Category.CommAlgCat.Local.Quotient
public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening

/-!
# Corepresentability of local flattening conditions

This module relates pointwise closed-fiber flatness after local base change to
corepresentability by quotients of the base local ring.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace LocalAlgCat.Flattening

variable (A : Type u) (B : Type u) (M : Type w)
variable [CommRing A]
variable [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [AddCommGroup M] [Module B M]

/-- A quotient of the base corepresents the closed-point flattening functor exactly when
closed-point flatness after every local base change is equivalent to annihilation of the
quotient ideal. -/
theorem corepresentableBy_quotient_iff [IsLocalRing A] (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) :
    Nonempty ((functor A B M).CorepresentableBy (LocalAlgCat.quotient A I hI)) ↔
      ∀ T : LocalAlgCat.{u} A,
        IsFlatAtClosedPoint A B M T ↔ I.map (algebraMap A T) = ⊥ := sorry

/-- For a henselian base, an essentially finite type local algebra, and a finite module,
closed-point flatness after local base change is characterized by annihilation of a fixed
ideal of the base. -/
theorem exists_corepresentingIdeal_spec [HenselianLocalRing A]
    [Algebra.EssFiniteType A B] [Module.Finite B M] :
    ∃ (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A),
      ∀ T : LocalAlgCat.{u} A,
        IsFlatAtClosedPoint A B M T ↔ I.map (algebraMap A T) = ⊥ := sorry

/-- For a henselian base, the closed-point flattening functor of a finite module over an
essentially finite type local algebra is corepresented by a quotient of the base. -/
theorem exists_corepresentingIdeal [HenselianLocalRing A]
    [Algebra.EssFiniteType A B] [Module.Finite B M] :
    ∃ (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A),
      Nonempty ((functor A B M).CorepresentableBy
        (LocalAlgCat.quotient A I hI)) := sorry

/-- Under essential finite-presentation hypotheses, the ideal corepresenting the closed-point
flattening functor can be chosen finitely generated. -/
theorem exists_fg_corepresentingIdeal [HenselianLocalRing A]
    [Algebra.EssFinitePresentation A B] [Module.FinitePresentation B M] :
    ∃ (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (_ : I.FG),
      Nonempty ((functor A B M).CorepresentableBy
        (LocalAlgCat.quotient A I hI)) := sorry

end LocalAlgCat.Flattening
