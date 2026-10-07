module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Finitely presented modules on schemes

This leaf owns the full subcategory of a scheme's module category consisting
of finitely presented modules. It is deliberately independent of a chosen
morphism: preservation under a particular pullback requires the hypotheses
provided by the relevant ringed-site pullback API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The object property on `X.Modules` selecting finitely presented modules. -/
abbrev finitePresentationModuleProperty (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun ℱ ↦ ℱ.IsFinitePresentation

/-- The full subcategory of finitely presented modules on a scheme `X`. -/
abbrev FinitePresentationModules (X : Scheme.{u}) : Type (u + 1) :=
  (finitePresentationModuleProperty X).FullSubcategory

namespace FinitePresentationModules

/-- The inclusion from finitely presented modules into all modules on `X`. -/
abbrev inclusion (X : Scheme.{u}) : FinitePresentationModules X ⥤ X.Modules :=
  (finitePresentationModuleProperty X).ι

/-- The underlying module of an object of `FinitePresentationModules X` is finitely
presented. -/
instance instIsFinitePresentation
    (X : Scheme.{u}) (ℱ : FinitePresentationModules X) :
    ℱ.obj.IsFinitePresentation := sorry

end FinitePresentationModules

end AlgebraicGeometry
