module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.CardinalGeneration.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.CardinalGeneration.Descent
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.SetTheory.Cardinal.Defs

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The quasi-coherent objects with cardinal-bounded local generation. -/
def kappaGenerated (κ : Cardinal.{u}) : pseudofunctor.ObjectProperty where
  prop X := fun (F : QCoh X.as.unop) ↦ F.obj.IsKappaGenerated κ

/-- The object property is cardinal-bounded local generation of the underlying sheaf. -/
theorem kappaGenerated_iff {κ : Cardinal.{u}} {X : LocallyDiscrete Scheme.{u}ᵒᵖ}
    {F : QCoh X.as.unop} :
    (kappaGenerated κ).prop X F ↔ F.obj.IsKappaGenerated κ := sorry

/-- Pullback preserves the cardinal-generated object property. -/
instance instIsClosedUnderMapObj_kappaGenerated (κ : Cardinal.{u}) :
    (kappaGenerated κ).IsClosedUnderMapObj := sorry

/-- Isomorphisms preserve the cardinal-generated object property. -/
instance instIsClosedUnderIsomorphisms_kappaGenerated (κ : Cardinal.{u}) :
    (kappaGenerated κ).IsClosedUnderIsomorphisms := sorry

/-- The cardinal-generated quasi-coherent pseudofunctor is a stack. -/
instance instIsStack (κ : Cardinal.{u}) [Fact (ℵ₀ ≤ κ)] :
    (kappaGenerated κ).fullsubcategory.IsStack fppfTopology := sorry

/-- The countable cardinal is a special case of the cardinal-generated stack. -/
theorem isStack_aleph0 :
    (kappaGenerated ℵ₀).fullsubcategory.IsStack fppfTopology := sorry

end AlgebraicGeometry.Scheme.QCoh
