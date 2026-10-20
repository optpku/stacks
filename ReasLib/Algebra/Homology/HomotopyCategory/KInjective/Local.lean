module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Injective Complexes as Homotopy-Local Objects

K-injectivity is the right-orthogonal formulation of locality at homotopy
quasi-isomorphisms. This leaf exposes that locality directly as a bijectivity
criterion on Hom-sets, without choosing a derived-category model.
-/

open CategoryTheory
open ComplexShape

universe v u

namespace CochainComplex.IsKInjective

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A cochain complex is K-injective exactly when precomposition by every quasi-isomorphism in the
homotopy category is bijective on morphisms into it. -/
@[stacks 070I]
theorem iff_precomp_bijective_of_quasiIso (I : CochainComplex A ℤ) :
    I.IsKInjective ↔
      ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (f : K ⟶ L),
        HomotopyCategory.quasiIso A (up ℤ) f →
          Function.Bijective
            (fun g : L ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I ↦ f ≫ g) := sorry


end CochainComplex.IsKInjective
