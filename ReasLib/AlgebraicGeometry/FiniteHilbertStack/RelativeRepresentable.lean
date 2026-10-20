module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Product
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.RelativeResIsom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction

/-!
# Representability of the relative finite Hilbert pairing

A representable target diagonal makes the positive-degree forgetful pairing
and its canonical test fibre products representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- For positive degree, the forgetful pairing
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` is representable by algebraic spaces whenever the
object diagonal of `𝒴` is representable by algebraic spaces. -/
theorem forgetToProduct.relativelyRepresentableByAlgebraicSpaces (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    (hd : 1 ≤ d)
    (h_diagonal : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (asGroupoidsOver 𝒴))) :
    relativelyRepresentableByAlgebraicSpaces (forgetToProduct F d) :=
  sorry

/-- For positive degree and a target stack with representable object diagonal,
the two-fibre product of the relative finite Hilbert stack with a represented
slice along fibre objects of the absolute finite Hilbert stack and the target
stack is representable by an algebraic space. -/
theorem relativeResIsom.isRepresentableByAlgebraicSpace (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    (hd : 1 ≤ d)
    (h_diagonal : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)))
    {U : Over S} (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    IsRepresentableByAlgebraicSpace (relativeResIsom F d ξ y) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
