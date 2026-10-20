module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.HomologyFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Preadditive

/-!
# Additive derived-abutment maps of Cartan--Eilenberg resolutions

The right-derived cohomology map attached to a resolution morphism depends only on its source
component and is additive in that component.  This leaf exposes the computation API and registers
the bundled derived-abutment functor as additive.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
variable [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)]

/-- Derived cohomology sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero derived-abutment map of a Cartan-Eilenberg resolution"]
theorem derivedHomology_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (n : ℤ) :
    derivedHomology F Q (zero : Map I J) n = 0 := sorry

/-- Derived cohomology preserves addition of resolution maps. -/
@[simp, stacks 015J "additive derived-abutment map of a Cartan-Eilenberg resolution"]
theorem derivedHomology_add (f g : Map I J) (n : ℤ) :
    derivedHomology F Q (f + g) n =
      derivedHomology F Q f n + derivedHomology F Q g n := sorry

/-- Derived cohomology preserves additive inverses. -/
@[simp]
theorem derivedHomology_neg (f : Map I J) (n : ℤ) :
    derivedHomology F Q (-f) n = -derivedHomology F Q f n := sorry

/-- Derived cohomology preserves subtraction. -/
@[simp]
theorem derivedHomology_sub (f g : Map I J) (n : ℤ) :
    derivedHomology F Q (f - g) n =
      derivedHomology F Q f n - derivedHomology F Q g n := sorry

/-- Derived cohomology preserves natural-number scalar multiplication. -/
@[simp]
theorem derivedHomology_nsmul (r : ℕ) (f : Map I J) (n : ℤ) :
    derivedHomology F Q (r • f) n = r • derivedHomology F Q f n := sorry

/-- Derived cohomology preserves integer scalar multiplication. -/
@[simp]
theorem derivedHomology_zsmul (r : ℤ) (f : Map I J) (n : ℤ) :
    derivedHomology F Q (r • f) n = r • derivedHomology F Q f n := sorry

end CochainComplex.CartanEilenbergResolution.Map

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
variable [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)]

/-- The bundled derived-abutment functor is additive in resolution morphisms. -/
@[stacks 015J "additivity of the derived-abutment functor"]
noncomputable instance derivedHomology_additive (n : ℤ) :
    (derivedHomology F Q n).Additive := sorry

end CochainComplex.CartanEilenbergResolution.Bundled
