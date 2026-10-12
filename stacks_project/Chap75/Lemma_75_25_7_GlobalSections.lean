/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import stacks_project.Chap75.Lemma_75_11_3_GlobalSections
public import stacks_project.Chap75.Lemma_75_8_4_Linear

/-!
# Derived global sections over an affine base

For an algebraic space `X` over a ring `A`, derived global sections `RΓ(X, -)`
land in `D(Γ(X, 𝒪_X))`. Restricting scalars along the structure map
`A →+* Γ(X, 𝒪_X)` yields the functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- Derived global sections of an algebraic space over `A`, as an object of `D(A)`. -/
abbrev globalSectionsOver
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    ModuleDerived X ⥤ DerivedCategory (ModuleCat.{u} A) :=
  moduleDerivedGlobalSections X ⋙
    CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f)

/-- `globalSectionsOver` is derived global sections followed by restriction of scalars
along `A →+* Γ(X, 𝒪_X)`. -/
theorem globalSectionsOver_def
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    globalSectionsOver f =
      moduleDerivedGlobalSections X ⋙
        CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f) :=
  sorry

/-- On objects, `globalSectionsOver` is `RΓ(X, E)` viewed in `D(A)`. -/
theorem globalSectionsOver_obj
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (E : ModuleDerived X) :
    (globalSectionsOver f).obj E =
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f)).obj
        ((moduleDerivedGlobalSections X).obj E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
