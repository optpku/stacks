module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A nonconstant morphism between curves over a field is dominant as a morphism of schemes. -/
theorem IsNonconstant.isDominant_of_curves
    {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
    [Curve X] [Curve Y] {f : X ⟶ Y} (hf : f.left.IsNonconstant) :
    IsDominant f.left := sorry

end AlgebraicGeometry.Scheme.Hom
