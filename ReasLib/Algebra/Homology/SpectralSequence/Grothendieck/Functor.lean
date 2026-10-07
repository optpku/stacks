module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map

/-!
# Functorial Grothendieck Spectral-Sequence Targets

The page-two and abutment targets are functorial in the bounded-below derived object.  This file
packages that functoriality using compositions of the canonical derived and homology functors,
while retaining the object and morphism APIs from `Basic` and `Map` as simp-normal forms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasInjectiveResolutions B]

/-- The action of `pageTwoFunctor` on a morphism is `pageTwoMap`. -/
@[simp, stacks 015N "Grothendieck spectral-sequence page-two functor"]
theorem pageTwoFunctor_map
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (p : ℕ) (q : ℤ) {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    (pageTwoFunctor G RF p q).map f = pageTwoMap G RF f p q := sorry

variable [HasDerivedCategory.{wC} C]

/-- The action of `abutmentFunctor` on a morphism is `abutmentMap`. -/
@[simp, stacks 015N "Grothendieck spectral-sequence abutment functor"]
theorem abutmentFunctor_map
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    (abutmentFunctor RGF n).map f = abutmentMap RGF f n := sorry

end CategoryTheory.Functor.RightDerived.Grothendieck
