module

public import ReasLib.CategoryTheory.Fibered.Groupoids.KernelPair.Operations
public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Representation

/-! # Representability of algebraic-stack kernel pairs -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory
universe u
namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}} {X U : GroupoidsOver S}

/-- The self two-fibre product of a morphism from a space-representable groupoid fibration
into an algebraic stack is representable by an algebraic space. -/
theorem kernelPair_isRepresentableByAlgebraicSpace (f : U ⟶ X) [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U) :
    IsRepresentableByAlgebraicSpace (KernelPair.kernelPair.{u + 1, u, u + 1} f) :=
  ⟨representedKernelPairSpace f hU, ⟨representedKernelPairEquiv f hU⟩⟩

end AlgebraicGeometry.AlgebraicStack
