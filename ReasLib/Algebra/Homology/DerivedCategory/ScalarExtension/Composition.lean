/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition

@[expose] public section

/-!
# Composition of derived extension of scalars

@stack 064M

This specializes the generic composition isomorphism for total left derived functors to module
extension of scalars.  It is the canonical comparison between iterated and direct derived scalar
extension.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.ModuleCat.DerivedExtension.Composition

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- The homotopy-to-derived functor for extension along `τ.comp σ` is canonically identified
with the composite model used for iterated derived extension. -/
noncomputable abbrev toDerivedIso (σ : R →+* A) (τ : A →+* B) :
    ModuleCat.extendScalarsToDerived.{u, u, max u v} (τ.comp σ) ≅
      (ModuleCat.extendScalars.{u, u, max u v} σ).mapHomotopyCategory (up ℤ) ⋙
        ModuleCat.extendScalarsToDerived.{u, u, max u v} τ :=
  Functor.LeftDerived.Homotopy.Composition.toDerivedIso
    (ModuleCat.extendScalars.{u, u, max u v} τ)
    (ModuleCat.extendScalars.{u, u, max u v} σ)
    (ModuleCat.extendScalars.{u, u, max u v} (τ.comp σ))
    (ModuleCat.extendScalarsComp.{u, v} σ τ)

/-- The counit exhibiting iterated derived extension as a left derived functor of extension
along `τ.comp σ`. -/
noncomputable abbrev counit (σ : R →+* A) (τ : A →+* B) :
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{max u v, u} R) (up ℤ) ⥤
        DerivedCategory (ModuleCat.{max u v, u} R)) ⋙
          (ModuleCat.derivedExtensionOfScalars.{u, u, max u v} σ ⋙
            ModuleCat.derivedExtensionOfScalars.{u, u, max u v} τ) ⟶
      (ModuleCat.extendScalars.{u, u, max u v} σ).mapHomotopyCategory (up ℤ) ⋙
        ModuleCat.extendScalarsToDerived.{u, u, max u v} τ :=
  Functor.LeftDerived.Homotopy.Composition.counit
    (ModuleCat.extendScalars.{u, u, max u v} τ)
    (ModuleCat.extendScalars.{u, u, max u v} σ)

/-- The canonical comparison from iterated derived extension to extension along the composite is
invertible.  This is the reusable instance needed to form the composition isomorphism without
reconstructing left-derived-functor witnesses at each use site. -/
@[stacks 064M "composition comparison for derived extension of scalars"]
instance comparison_isIso (σ : R →+* A) (τ : A →+* B) :
    IsIso (Functor.LeftDerived.Homotopy.Composition.comparison
      (ModuleCat.extendScalars.{u, u, max u v} τ)
      (ModuleCat.extendScalars.{u, u, max u v} σ)
      (ModuleCat.extendScalars.{u, u, max u v} (τ.comp σ))
      (ModuleCat.extendScalarsComp.{u, v} σ τ)) := sorry

/-- The canonical comparison from iterated derived extension to extension along the composite
ring homomorphism. -/
noncomputable abbrev iso (σ : R →+* A) (τ : A →+* B) :
    ModuleCat.derivedExtensionOfScalars.{u, u, max u v} σ ⋙
        ModuleCat.derivedExtensionOfScalars.{u, u, max u v} τ ≅
      ModuleCat.derivedExtensionOfScalars.{u, u, max u v} (τ.comp σ) :=
  Functor.LeftDerived.Homotopy.Composition.iso
    (ModuleCat.extendScalars.{u, u, max u v} τ)
    (ModuleCat.extendScalars.{u, u, max u v} σ)
    (ModuleCat.extendScalars.{u, u, max u v} (τ.comp σ))
    (ModuleCat.extendScalarsComp.{u, v} σ τ)

/-- The derived-extension composition isomorphism is characterized by its equation with the
canonical total-left-derived counits. -/
theorem iso_hom_counit (σ : R →+* A) (τ : A →+* B) :
    Functor.whiskerLeft
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat.{max u v, u} R) (up ℤ) ⥤
            DerivedCategory (ModuleCat.{max u v, u} R))
        (iso σ τ).hom ≫
      ModuleCat.derivedExtensionOfScalarsCounit.{u, u, max u v} (τ.comp σ) =
        counit σ τ ≫ (toDerivedIso σ τ).inv := sorry

/-- The componentwise counit equation characterizing the derived-extension composition
isomorphism. -/
theorem iso_hom_counit_app (σ : R →+* A) (τ : A →+* B)
    (K : HomotopyCategory (ModuleCat.{max u v, u} R) (up ℤ)) :
    (iso σ τ).hom.app
        ((DerivedCategory.Qh :
          HomotopyCategory (ModuleCat.{max u v, u} R) (up ℤ) ⥤
            DerivedCategory (ModuleCat.{max u v, u} R)).obj K) ≫
      (ModuleCat.derivedExtensionOfScalarsCounit.{u, u, max u v} (τ.comp σ)).app K =
        (counit σ τ).app K ≫ (toDerivedIso σ τ).inv.app K := sorry

end

end CategoryTheory.ModuleCat.DerivedExtension.Composition

namespace CategoryTheory.ModuleCat

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- The canonical iterated-to-direct derived-extension isomorphism, transported to a named
composite `ρ`. -/
noncomputable abbrev derivedExtensionOfScalarsCompIso
    (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B) (hcomp : τ.comp σ = ρ) :
    ModuleCat.derivedExtensionOfScalars.{u, u, max u v} σ ⋙
        ModuleCat.derivedExtensionOfScalars.{u, u, max u v} τ ≅
      ModuleCat.derivedExtensionOfScalars.{u, u, max u v} ρ :=
  CategoryTheory.ModuleCat.DerivedExtension.Composition.iso.{u, v} σ τ ≪≫
    eqToIso (congrArg (fun f ↦ ModuleCat.derivedExtensionOfScalars.{u, u, max u v} f) hcomp)

/-- The canonical comparison morphism from iterated to direct derived scalar extension. -/
noncomputable def derivedExtensionOfScalarsCompComparison
    (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B) (hcomp : τ.comp σ = ρ) :
    ModuleCat.derivedExtensionOfScalars.{u, u, max u v} σ ⋙
        ModuleCat.derivedExtensionOfScalars.{u, u, max u v} τ ⟶
      ModuleCat.derivedExtensionOfScalars.{u, u, max u v} ρ :=
  (ModuleCat.derivedExtensionOfScalarsCompIso σ τ ρ hcomp).hom

end

end CategoryTheory.ModuleCat
