module

public import ReasLib.NumberTheory.Automorphic.Eigenform

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.SchemeOverField
universe u v
namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k] {Λ : Type v} [CommRing Λ]
variable (X : SchemeOverField k)

/-! Compatibility checks for the chapter-facing eigenvalue API. -/
#check (Eigenform X Λ)
#check (Eigenform.of X : (t : closedPoints X.left → Λ) → (u : closedPoints X.left → Λˣ) → Eigenform X Λ)
#check (Eigenform.t_apply X : ∀ (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ),
  (Eigenform.of X t u).t = t)
#check (Eigenform.u_apply X : ∀ (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ),
  (Eigenform.of X t u).u = u)
#check (Eigenform.spec X : ∀ f : Eigenform X Λ, f = Eigenform.of X f.t f.u)

end AlgebraicGeometry.SchemeOverField
