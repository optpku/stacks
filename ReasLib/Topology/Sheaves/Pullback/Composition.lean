module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Topology.Sheaves.Functors

/-!
# Composition of pullback functors

This file constructs the canonical comparison for pullback along a composite continuous map,
together with its associativity coherence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe w v u

namespace TopCat.Sheaf

variable {A : Type u} [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- Pullback functors along equal continuous maps are canonically isomorphic. -/
def pullbackCongr {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) :
    pullback A f ≅ pullback A g :=
  eqToIso (congrArg (pullback A) h)

/-- Pullback of sheaves along a composite continuous map is canonically isomorphic to the
composite of the two pullback functors. -/
def pullbackComp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback A g ⋙ pullback A f ≅ pullback A (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction A g)
    (pullbackPushforwardAdjunction A f)
    (pullbackPushforwardAdjunction A (f ≫ g))
    (Iso.refl _)

/-- The canonical pullback-composition comparisons for sheaves satisfy the associativity
coherence law. -/
theorem pullback_assoc {W X Y Z : TopCat.{w}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft _ (pullbackComp (A := A) f g) ≪≫
        pullbackComp (A := A) (f ≫ g) h =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pullbackComp (A := A) g h) _ ≪≫
          pullbackComp (A := A) f (g ≫ h) := sorry

/-- Componentwise hom form of associativity coherence for sheaf pullback. -/
theorem pullback_assoc_hom_app {W X Y Z : TopCat.{w}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Z.Sheaf A) :
    (pullback A f).map ((pullbackComp (A := A) g h).hom.app F) ≫
        (pullbackComp (A := A) f (g ≫ h)).hom.app F =
      (pullbackComp (A := A) f g).hom.app ((pullback A h).obj F) ≫
        (pullbackComp (A := A) (f ≫ g) h).hom.app F := sorry

end TopCat.Sheaf

namespace TopCat.Presheaf

variable {C : Type u} [Category.{w} C] [HasColimits C]

/-- Presheaf pullback functors along equal continuous maps are canonically isomorphic. -/
def pullbackCongr {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) :
    pullback C f ≅ pullback C g :=
  eqToIso (congrArg (pullback C) h)

/-- Pullback of presheaves along a composite continuous map is canonically isomorphic to the
composite of the two pullback functors. -/
def pullbackComp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback C g ⋙ pullback C f ≅ pullback C (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction C g)
    (pullbackPushforwardAdjunction C f)
    (pullbackPushforwardAdjunction C (f ≫ g))
    (Iso.refl _)

end TopCat.Presheaf
