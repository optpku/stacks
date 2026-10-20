module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- For composable morphisms of schemes, the Jacobi–Zariski six-term naive-cotangent
sequence is exact, including exactness at its final term before zero. -/
theorem sixTerm_exact {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    t.sixTerm.Exact ∧ Epi (HomologicalComplex.homologyMap t.comparison 0) := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
