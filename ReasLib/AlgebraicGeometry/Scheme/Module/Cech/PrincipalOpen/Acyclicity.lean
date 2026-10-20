module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace ModuleCech

/-- The extended Čech complex associated to finitely many principal opens and a module sheaf is
acyclic after restriction to the union of those principal opens. -/
theorem ofSections_restrict_acyclic {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (((Scheme.Modules.restrictFunctor (⨆ i, X.basicOpen (f i)).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (ofSections f ℱ)).Acyclic := sorry

end ModuleCech

end
