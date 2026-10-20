module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import ReasLib.Topology.Sheaves.Preadditive
public import ReasLib.Topology.Sheaves.Pushforward.SectionFamilies
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaf pushforward constructions

Canonical entry point for pushforward (direct image) sheaf constructions.
- Section-level description of pushforward families
- Functoriality and equivalences induced by isomorphisms of spaces
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe w v u

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}}

/-- Push a presheaf forward and then sheafify it on the target space. -/
@[stacks 0A3E "sheafified presheaf pushforward"]
noncomputable abbrev sheafifiedPushforward
    [HasWeakSheafify (Opens.grothendieckTopology Y) C] (f : X ⟶ Y) :
    X.Presheaf C ⥤ Y.Sheaf C :=
  pushforward C f ⋙ presheafToSheaf (Opens.grothendieckTopology Y) C

/-- Presheaf pushforward preserves sectionwise addition of morphisms. -/
instance pushforward_additive [Preadditive C] (f : X ⟶ Y) :
    (pushforward C f).Additive where
  map_add := rfl

/-- Pushforward is additive for the canonical abelian structures on presheaf categories. -/
instance pushforward_additive_of_abelian [Abelian C] (f : X ⟶ Y) :
    (pushforward C f).Additive where
  map_add := rfl

/-- Sheafified pushforward is additive whenever pushforward and sheafification are additive. -/
instance sheafifiedPushforward_additive [Preadditive C]
    [HasWeakSheafify (Opens.grothendieckTopology Y) C]
    [(presheafToSheaf (Opens.grothendieckTopology Y) C).Additive] (f : X ⟶ Y) :
    (sheafifiedPushforward (C := C) f).Additive :=
  inferInstanceAs
    (((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ C).obj (Opens.map f).op) ⋙
      presheafToSheaf (Opens.grothendieckTopology Y) C).Additive

/-- Sheafified pushforward is additive for the canonical abelian structures. -/
instance sheafifiedPushforward_additive_of_abelian [Abelian C]
    [HasSheafify (Opens.grothendieckTopology Y) C] (f : X ⟶ Y) :
    (sheafifiedPushforward (C := C) f).Additive :=
  inferInstanceAs
    (((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ C).obj (Opens.map f).op) ⋙
      presheafToSheaf (Opens.grothendieckTopology Y) C).Additive

/-- Sheafified pushforward of abelian-group-valued presheaves preserves finite limits. -/
noncomputable instance sheafifiedPushforward_preservesFiniteLimits
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{w}] (f : X ⟶ Y) :
    PreservesFiniteLimits
      (sheafifiedPushforward (C := AddCommGrpCat.{w}) f) := sorry

/-- Sheafified pushforward of abelian-group-valued presheaves preserves finite colimits. -/
noncomputable instance sheafifiedPushforward_preservesFiniteColimits
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{w}] (f : X ⟶ Y) :
    PreservesFiniteColimits
      (sheafifiedPushforward (C := AddCommGrpCat.{w}) f) := sorry

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X Y Z : TopCat.{w}}

/-- Sheaf pushforward is recovered by pushing forward the underlying presheaf and then
sheafifying. -/
@[stacks 0A3E "pushforward through presheaf sheafification"]
noncomputable def pushforwardSheafificationIso
    [HasWeakSheafify (Opens.grothendieckTopology Y) C] (f : X ⟶ Y) :
    forget C X ⋙ TopCat.Presheaf.sheafifiedPushforward (C := C) f ≅
      pushforward C f :=
  (Functor.associator
    (forget C X)
    (TopCat.Presheaf.pushforward C f)
    (presheafToSheaf (Opens.grothendieckTopology Y) C)).symm ≪≫
    Functor.isoWhiskerRight
      (pushforwardForgetIso C f).symm
      (presheafToSheaf (Opens.grothendieckTopology Y) C) ≪≫
    Functor.associator
      (pushforward C f)
      (forget C Y)
      (presheafToSheaf (Opens.grothendieckTopology Y) C) ≪≫
    Functor.isoWhiskerLeft
      (pushforward C f)
      (sheafificationNatIso (Opens.grothendieckTopology Y) C).symm ≪≫
    (pushforward C f).rightUnitor

/-- Sheaf pushforward preserves sectionwise addition of morphisms. -/
instance pushforward_additive [Preadditive C] (f : X ⟶ Y) :
    (pushforward C f).Additive where
  map_add := rfl

/-- Pushforward is additive for the canonical abelian structures on sheaf categories. -/
instance pushforward_additive_of_abelian [Abelian C]
    [HasSheafify (Opens.grothendieckTopology X) C]
    [HasSheafify (Opens.grothendieckTopology Y) C] (f : X ⟶ Y) :
    (pushforward C f).Additive where
  map_add := rfl

/-- Pushforward along the identity map is the identity functor on sheaves. -/
@[simp]
theorem pushforward_id (X : TopCat.{w}) :
    pushforward C (𝟙 X) = 𝟭 (X.Sheaf C) := sorry

/-- Successive sheaf pushforwards agree with pushforward along the composite map. -/
@[simp]
theorem pushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward C f ⋙ pushforward C g = pushforward C (f ≫ g) := sorry

/-- Pushforward along an isomorphism of spaces is an equivalence between their categories of
sheaves. -/
noncomputable def pushforwardEquivalence (f : X ⟶ Y) [IsIso f] :
    X.Sheaf C ≌ Y.Sheaf C :=
  CategoryTheory.Equivalence.mk (pushforward C f) (pushforward C (inv f))
    (eqToIso (congrArg (pushforward C) (IsIso.hom_inv_id f))).symm
    (eqToIso (congrArg (pushforward C) (IsIso.inv_hom_id f)))

/-- The forward functor of `pushforwardEquivalence f` is pushforward along `f`. -/
@[simp]
theorem pushforwardEquivalence_functor (f : X ⟶ Y) [IsIso f] :
    (pushforwardEquivalence (C := C) f).functor = pushforward C f := sorry

/-- The inverse functor of `pushforwardEquivalence f` is pushforward along `inv f`. -/
@[simp]
theorem pushforwardEquivalence_inverse (f : X ⟶ Y) [IsIso f] :
    (pushforwardEquivalence (C := C) f).inverse = pushforward C (inv f) := sorry

/-- Pushforward along an isomorphism is recognized automatically as an equivalence of
categories. -/
noncomputable instance pushforwardIsEquivalence (f : X ⟶ Y) [IsIso f] :
    (pushforward C f).IsEquivalence :=
  (pushforwardEquivalence (C := C) f).isEquivalence_functor

/-- Pushforward along an isomorphism preserves finite limits and finite colimits. -/
theorem pushforward_exact_of_isIso (f : X ⟶ Y) [IsIso f] :
    exactFunctor (X.Sheaf C) (Y.Sheaf C) (pushforward C f) := sorry

end TopCat.Sheaf
