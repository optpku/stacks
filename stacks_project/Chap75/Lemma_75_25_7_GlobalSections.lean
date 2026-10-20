module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import stacks_project.Chap75.Lemma_75_11_3_GlobalSections
public import stacks_project.Chap75.Lemma_75_8_4_Linear
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.OverAffine

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

/- Derived global sections over an affine base. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.globalSectionsOver :
  ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))},
    (X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) →
      ModuleDerived X ⥤ DerivedCategory (ModuleCat.{u} A))

/- The defining functor equation for derived global sections over an affine base. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.globalSectionsOver_def :
  ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))),
    globalSectionsOver f =
      moduleDerivedGlobalSections X ⋙
        CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f))

/- The object equation for derived global sections over an affine base. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.globalSectionsOver_obj :
  ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (E : ModuleDerived X),
    (globalSectionsOver f).obj E =
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars (Hom.globalSectionsMap f)).obj
        ((moduleDerivedGlobalSections X).obj E))

end AlgebraicGeometry.AlgebraicSpace.Modules
