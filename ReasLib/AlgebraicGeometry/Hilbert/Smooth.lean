module

public import ReasLib.AlgebraicGeometry.Hilbert.AddPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/-- If `X ⟶ S` is a smooth relative curve and all its Hilbert functors are representable, then
the degree-`d` representing scheme is smooth over `S` of relative dimension `d`. -/
@[instance]
theorem representingScheme_smoothOfRelativeDimension {S : Scheme.{u}} (X : Over S)
    [SmoothOfRelativeDimension 1 X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    SmoothOfRelativeDimension d (functor X d).reprX.hom := sorry

end AlgebraicGeometry.Hilbert
