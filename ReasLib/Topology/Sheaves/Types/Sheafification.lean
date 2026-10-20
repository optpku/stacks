module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Separation and sheafification for type-valued presheaves

The site-theoretic predicate `Presieve.IsSeparated` and the canonical sheafification functor are
the primitive notions here.  The concrete criteria are exposed as small bridges for topological
spaces, without introducing a parallel sheafification API.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open TopCat.Presheaf.Sheafify

universe u

noncomputable section

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- A `Type`-valued presheaf is separated exactly when its sections inject into the family of
germs on every open subset. -/
@[stacks 007A "separated presheaf iff stalk-family injective"]
theorem isSeparated_iff_injective_toStalkFamily (ℱ : X.Presheaf (Type u)) :
    Presieve.IsSeparated (Opens.grothendieckTopology X) ℱ ↔
      ∀ U : Opens X, Function.Injective (fun s ↦ (ℱ.toSheafify.app (op U) s).1) := sorry

/-- A `Type`-valued presheaf is separated exactly when its sheafification unit is sectionwise
injective. -/
theorem isSeparated_iff_toSheafify_injective (ℱ : X.Presheaf (Type u)) :
    Presieve.IsSeparated (Opens.grothendieckTopology X) ℱ ↔
      ∀ U : Opens X, Function.Injective (ℱ.toSheafify.app (op U)) := sorry

/-- Sections of a type-valued sheaf are determined by their germs at points of an open subset. -/
theorem sectionToStalkFamily_injective (ℱ : X.Sheaf (Type u)) (U : Opens X) :
    Function.Injective (fun s ↦ (ℱ.presheaf.toSheafify.app (op U) s).1) := sorry

/-- The map from sections of a type-valued sheafification over `U` to their values in the
original stalks. -/
def sheafifySectionToStalks (F : X.Presheaf (Type u)) (U : Opens X) :
    F.sheafify.presheaf.obj (op U) ⟶ ∀ x : U, F.stalk x.1 :=
  ↾fun s (x : U) ↦ F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s)

/-- The map taking a section of the presheaf of stalk families to its germs at points of `U`. -/
def stalkSectionsToStalks (F : X.Presheaf (Type u)) (U : Opens X) :
    (X.presheafToTypes fun x ↦ F.stalk x).obj (op U) ⟶
      ∀ x : U, (X.presheafToTypes fun y ↦ F.stalk y).stalk x.1 :=
  ↾fun s (x : U) ↦ (X.presheafToTypes fun y ↦ F.stalk y).germ U x.1 x.2 s

/-- The product over `x ∈ U` of the stalk maps induced by the canonical map from `F` to the
presheaf of its stalk families. -/
def stalksToStalkSectionStalks (F : X.Presheaf (Type u)) (U : Opens X) :
    (∀ x : U, F.stalk x.1) ⟶
      ∀ x : U, (X.presheafToTypes fun y ↦ F.stalk y).stalk x.1 :=
  ↾fun s (x : U) ↦
    ((stalkFunctor (Type u) x.1).map
      (F.toSheafify ≫
        subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) (s x)

/-- Sections of a type-valued sheafification over an open subset form the pullback of the
corresponding sections of the stalk-family presheaf and the original stalk values. -/
theorem sheafifySectionIsPullback (F : X.Presheaf (Type u)) (U : Opens X) :
    IsPullback
      ((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U))
      (sheafifySectionToStalks F U)
      (stalkSectionsToStalks F U)
      (stalksToStalkSectionStalks F U) := sorry

section

variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable {F G : X.Presheaf (Type u)} (φ : F ⟶ G)

/-- A sectionwise-surjective morphism of `Type`-valued presheaves becomes locally surjective after
sheafification.

This is the direct consumer bridge obtained from mathlib's
`Presheaf.isLocallySurjective_of_surjective` and
`Presheaf.isLocallySurjective_presheafToSheaf_map_iff`. -/
theorem isLocallySurjective_presheafToSheaf_map_of_app_surjective
    (hφ : ∀ U : Opens X, Function.Surjective (φ.app (op U))) :
    CategoryTheory.Sheaf.IsLocallySurjective
      ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ) := sorry

/-- A sectionwise-injective morphism of `Type`-valued presheaves becomes sectionwise injective
after sheafification.

This is the direct consumer bridge obtained from mathlib's local-injectivity preservation theorem
and `CategoryTheory.Sheaf.isLocallyInjective_iff_injective`. -/
theorem app_injective_presheafToSheaf_map_of_app_injective
    (hφ : ∀ U : Opens X, Function.Injective (φ.app (op U))) :
    ∀ U : Opens X, Function.Injective
      (((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ).hom.app (op U)) := sorry

end

end TopCat.Presheaf
