/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Special-fibre inclusion and small étale global-section restriction

`Spec(A / I)` as an algebraic space over `Spec A`, its structure morphism, and
the canonical restriction of compatible sections along a morphism of algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- `Spec(A / I)` viewed as an algebraic space over `Spec A`. -/
def ofOverSpecQuotient {A : Type u} [CommRing A] (I : Ideal A) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ofOver (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))

/-- `ofOverSpecQuotient I` is `ofOver` of `Spec.map` of `Ideal.Quotient.mk I`. -/
theorem ofOverSpecQuotient_eq {A : Type u} [CommRing A] (I : Ideal A) :
    ofOverSpecQuotient I =
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :=
  rfl

/-- The morphism `Spec(A / I) ⟶ Spec A` in `AlgebraicSpace (Spec A)`. -/
def ofOverSpecQuotientι {A : Type u} [CommRing A] (I : Ideal A) :
    ofOverSpecQuotient I ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (Category.comp_id _)

/-- `ofOverSpecQuotientι I` is `ofOverHomMk` of `Spec.map` of `Ideal.Quotient.mk I`. -/
theorem ofOverSpecQuotientι_eq {A : Type u} [CommRing A] (I : Ideal A) :
    ofOverSpecQuotientι I =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Category.comp_id _) :=
  rfl

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

/-- `smallEtaleGlobalSectionsPullback` is `pushforwardSectionsEquiv` of the
image of the adjunction unit under `sectionsFunctor`. -/
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
