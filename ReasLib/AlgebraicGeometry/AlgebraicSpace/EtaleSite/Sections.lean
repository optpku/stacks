/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos

/-!
# Restriction of small étale global sections

A morphism of algebraic spaces induces a canonical restriction of compatible
sections to the inverse-image sheaf on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Canonical restriction `Γ(X, F) → Γ(Y, f⁻¹ F)` of compatible sections along a
morphism of algebraic spaces, obtained from the adjunction unit of
`smallEtaleMorphismOfTopoi f` and the global-section identification of its
direct image. -/
def smallEtaleGlobalSectionsPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    F.obj.sections →
      ((smallEtaleMorphismOfTopoi f).inverseImage.obj F).obj.sections :=
  fun s ↦
    (smallEtaleMorphismOfTopoi f).pushforwardSectionsEquiv
        ((smallEtaleMorphismOfTopoi f).inverseImage.obj F)
      ((Functor.sectionsFunctor _).map
        ((smallEtaleMorphismOfTopoi f).adjunction.unit.app F).hom s)

/-- Restriction of compatible sections is the direct-image section equivalence
applied to the image of the adjunction unit under the sections functor. -/
theorem smallEtaleGlobalSectionsPullback_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtaleGlobalSectionsPullback f F =
      fun s ↦
        (smallEtaleMorphismOfTopoi f).pushforwardSectionsEquiv
            ((smallEtaleMorphismOfTopoi f).inverseImage.obj F)
          ((Functor.sectionsFunctor _).map
            ((smallEtaleMorphismOfTopoi f).adjunction.unit.app F).hom s) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
