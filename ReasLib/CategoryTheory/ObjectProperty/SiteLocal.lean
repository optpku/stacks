module

public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal

public section

universe v u

namespace CategoryTheory.ObjectProperty.IsLocal

variable {C : Type u} [Category.{v} C]

/-- An object property is local for a precoverage containing singleton isomorphism covers
if and only if it holds on an object exactly when it holds on every member of each covering
family. -/
theorem iff_forall_zeroHypercover (P : ObjectProperty C) (K : Precoverage C) [K.HasIsos] :
    P.IsLocal K ↔
      ∀ ⦃X : C⦄ (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P X ↔ ∀ i, P (𝒰.X i) := sorry

end CategoryTheory.ObjectProperty.IsLocal
