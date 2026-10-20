module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Isomorphism
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace CochainComplex.IsKFlat

/-- The degreewise tilde complex associated to a K-flat cochain complex of modules over a
commutative ring is K-flat. -/
theorem tilde {R : CommRingCat.{u}} {K : CochainComplex (ModuleCat R) ℤ}
    (hK : K.IsKFlat) :
    (((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (up ℤ)).obj K).IsKFlat := sorry

end CochainComplex.IsKFlat
