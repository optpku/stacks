module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Ordered.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace ModuleCech

variable {X : Scheme.{u}}

/-- The bounded principal-open Čech complex, functorial in its module argument. -/
noncomputable def ofSectionsFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ CochainComplex X.Modules ℕ :=
  AlgebraicGeometry.Scheme.ModuleCech.Ordered.extendedFunctor
    (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down))

/-- Evaluating the principal-open Čech functor recovers `ofSections`. -/
theorem ofSectionsFunctor_obj {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (ofSectionsFunctor f).obj ℱ = ofSections f ℱ := sorry

/-- The natural projection from the principal-open Čech complex to its degree-zero module. -/
noncomputable def ofSectionsProjection {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    ofSectionsFunctor f ⟶ CochainComplex.single₀ X.Modules :=
  AlgebraicGeometry.Scheme.ModuleCech.Ordered.projection
    (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down))

end ModuleCech

end
