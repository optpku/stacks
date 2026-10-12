/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Operations on Homotopies of Differential Graded Module Maps

Concrete homotopies of DG-module maps are closed under addition and under composition on either
side.  These operations are the reusable interface needed to assemble contractions of direct
sum decompositions without exposing graded-Hom degree casts at every call site.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule
namespace Homotopy

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {K L M : DifferentialGradedModule.{u, w} A}

/-- The sum of two concrete homotopies is the degreewise sum of their homogeneous witnesses. -/
def add {f₁ g₁ f₂ g₂ : K ⟶ L} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) :
    Homotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  condition := sorry

/-- Postcomposition carries a concrete homotopy to a concrete homotopy. -/
def compRight {f g : K ⟶ L} (h : Homotopy f g) (k : L ⟶ M) :
    Homotopy (f ≫ k) (g ≫ k) where
  hom := cast (congrArg (GradedHom A K M) (add_zero (-1)))
    (gradedHomComp (homToCompHom k).val h.hom)
  condition := sorry

/-- Precomposition carries a concrete homotopy to a concrete homotopy. -/
def compLeft {f g : L ⟶ M} (h : Homotopy f g) (k : K ⟶ L) :
    Homotopy (k ≫ f) (k ≫ g) where
  hom := cast (congrArg (GradedHom A K M) (zero_add (-1)))
    (gradedHomComp h.hom (homToCompHom k).val)
  condition := sorry

end Homotopy
end DifferentialGradedModule
