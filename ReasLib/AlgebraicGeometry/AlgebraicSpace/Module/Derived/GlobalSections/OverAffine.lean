/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine

/-!
# Derived global sections over an affine base

Derived global sections followed by restriction of scalars along the structure map
take derived modules on an algebraic space over `A` to `D(A)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- Derived global sections of an algebraic space over `A`, valued in `D(A)`. -/
abbrev globalSectionsOver
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    ModuleDerived X ⥤ DerivedCategory (ModuleCat.{u} A) :=
  moduleDerivedGlobalSections X ⋙
    CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f)

/-- Derived global sections over `A` is the composite of derived global sections and
restriction of scalars along `A →+* Γ(X, 𝒪_X)`. -/
theorem globalSectionsOver_def
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    globalSectionsOver f =
      moduleDerivedGlobalSections X ⋙
        CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f) :=
  rfl

/-- On objects, derived global sections over `A` is `RΓ(X, E)` with scalars restricted
along the structure map. -/
theorem globalSectionsOver_obj
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (E : ModuleDerived X) :
    (globalSectionsOver f).obj E =
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f)).obj
        ((moduleDerivedGlobalSections X).obj E) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
