module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Transport of completions along an equality of closed subsets. -/
def congrClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T₁ T₂ : Closeds (Points X)} (h : T₁ = T₂) :
    completionAlong X T₁ ⟶ completionAlong X T₂ :=
  eqToHom (congrArg (completionAlong X) h)

/-- `congrClosed h` is identity transport of `completionAlong` along `h`. -/
theorem congrClosed_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T₁ T₂ : Closeds (Points X)} (h : T₁ = T₂) :
    congrClosed h = eqToHom (congrArg (completionAlong X) h) :=
  rfl

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
