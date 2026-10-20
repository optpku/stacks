/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback

/-!
# Pullback of algebraic-space descent data along a morphism of families

A morphism of fixed-target families of algebraic spaces over a scheme `S` induces a
pullback functor on descent data. Morphisms over the same base map give canonically
isomorphic functors, and the construction agrees with singleton-family pullback along
the induced map of coproducts.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S}

section Family

variable {I : Type v} {I' : Type w}
variable {Xᵢ : I → AlgebraicSpace S} {X'ᵢ : I' → AlgebraicSpace S}
variable {f : ∀ i, Xᵢ i ⟶ X} {f' : ∀ i, X'ᵢ i ⟶ X'}
variable {g : X' ⟶ X}

/-- Pullback of algebraic-space descent data along a morphism of fixed-target families. -/
noncomputable def functorOfHom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) :
    DescentData Xᵢ f ⥤ DescentData X'ᵢ f' :=
  Pseudofunctor.DescentData.pullFunctor (overPseudofunctor S) comm

/-- The component at `i` of a pulled descent datum is slice pullback along the corresponding
component of the family morphism. -/
theorem functorOfHom_obj_obj (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
    (D : DescentData Xᵢ f) (i : I') :
    ((functorOfHom α gᵢ comm).obj D).obj i =
      (overPullback (gᵢ i)).obj (D.obj (α i)) := sorry

/-- The transition map of a pulled descent datum is the canonical pseudofunctorial pullback of
the original transition map. -/
theorem functorOfHom_obj_hom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
    (D : DescentData Xᵢ f) {Z : AlgebraicSpace S} (q : Z ⟶ X') {i j : I'}
    (h₀ : Z ⟶ X'ᵢ i) (h₁ : Z ⟶ X'ᵢ j)
    (hh₀ : h₀ ≫ f' i = q) (hh₁ : h₁ ≫ f' j = q) :
    ((functorOfHom α gᵢ comm).obj D).hom q h₀ h₁ hh₀ hh₁ =
      Pseudofunctor.DescentData.pullFunctorObjHom (F := overPseudofunctor S)
        (f := f) (p := g) (f' := f') (α := α) (p' := gᵢ) (w := comm)
        D q h₀ h₁ hh₀ hh₁ := sorry

/-- Pullback of a morphism of algebraic-space descent data acts componentwise by slice pullback
along the corresponding component of the family morphism. -/
theorem functorOfHom_map_hom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
    {D E : DescentData Xᵢ f} (η : D ⟶ E) (i : I') :
    ((functorOfHom α gᵢ comm).map η).hom i =
      (overPullback (gᵢ i)).map (η.hom (α i)) := sorry

/-- Two morphisms of fixed-target algebraic-space families over the same base map induce
canonically isomorphic pullback functors on descent data. -/
noncomputable def isoOfHom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
    (β : I' → I) (hᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (β i))
    (comm' : ∀ i, hᵢ i ≫ f (β i) = f' i ≫ g) :
    functorOfHom α gᵢ comm ≅ functorOfHom β hᵢ comm' :=
  Pseudofunctor.DescentData.pullFunctorIso (F := overPseudofunctor S)
    (f := f) (p := g) (f' := f') (α := α) (p' := gᵢ) (w := comm)
    (β := β) (p'' := hᵢ) comm'

/-- The forward same-base comparison at `i` is the descent-data comparison between the two
chosen component maps. -/
theorem isoOfHom_hom_app_hom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
    (β : I' → I) (hᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (β i))
    (comm' : ∀ i, hᵢ i ≫ f (β i) = f' i ≫ g)
    (D : DescentData Xᵢ f) (i : I') :
    ((isoOfHom α gᵢ comm β hᵢ comm').hom.app D).hom i =
      D.hom (f' i ≫ g) (gᵢ i) (hᵢ i) (comm i) (comm' i) := sorry

end Family

section Coproduct

variable {I : Type v} {I' : Type v}
variable {Xᵢ : I → AlgebraicSpace S} {X'ᵢ : I' → AlgebraicSpace S}
variable {f : ∀ i, Xᵢ i ⟶ X} {f' : ∀ i, X'ᵢ i ⟶ X'}
variable {g : X' ⟶ X}
variable [Small.{u} I] [Small.{u} I']

/-- The morphism of coproducts induced by a morphism of fixed-target algebraic-space families. -/
noncomputable def coproductMapOfHom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) :
    coproduct X'ᵢ ⟶ coproduct Xᵢ :=
  coproductDesc fun i ↦ gᵢ i ≫ coproductι Xᵢ (α i)

/-- The induced coproduct map restricts on the `i`-th summand to the corresponding component map
followed by the target coproduct injection. -/
theorem coproductMapOfHom_ι (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) (i : I') :
    coproductι X'ᵢ i ≫ coproductMapOfHom α gᵢ =
      gᵢ i ≫ coproductι Xᵢ (α i) := sorry

/-- The induced coproduct map and the base map form a commutative square with the two coproduct
arrows. -/
theorem coproductMapOfHom_fac (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) :
    coproductMapOfHom α gᵢ ≫ coproductArrow Xᵢ f PUnit.unit =
      coproductArrow X'ᵢ f' PUnit.unit ≫ g := sorry

/-- Pullback through a source coproduct injection and then through the induced coproduct map
lies over the base map. -/
theorem coproductMapOfHom_left_fac (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) (i : I') :
    (coproductι X'ᵢ i ≫ coproductMapOfHom α gᵢ) ≫ coproductArrow Xᵢ f PUnit.unit =
      f' i ≫ g := sorry

/-- Pullback through a component map and its target coproduct injection lies over the base map. -/
theorem coproductMapOfHom_right_fac (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) (i : I') :
    (gᵢ i ≫ coproductι Xᵢ (α i)) ≫ coproductArrow Xᵢ f PUnit.unit = f' i ≫ g := sorry

/-- Pulling back from the target coproduct first through the induced coproduct map and then
through the source coproduct injections is compatible with componentwise family pullback. -/
noncomputable def coproductRestrictionIsoOfHom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) :
    functor (coproductArrow Xᵢ f PUnit.unit) (coproductArrow X'ᵢ f' PUnit.unit) g
          (coproductMapOfHom α gᵢ) (CommSq.mk (coproductMapOfHom_fac α gᵢ comm)) ⋙
        restrictCoproduct X'ᵢ f' ≅
      restrictCoproduct Xᵢ f ⋙ functorOfHom α gᵢ comm :=
  Pseudofunctor.DescentData.pullFunctorCompIso (F := overPseudofunctor S)
      (f := fun _ : PUnit.{v + 1} ↦ coproductArrow Xᵢ f PUnit.unit) (p := g)
      (f' := fun _ : PUnit.{v + 1} ↦ coproductArrow X'ᵢ f' PUnit.unit)
      (α := fun _ ↦ PUnit.unit) (p' := fun _ ↦ coproductMapOfHom α gᵢ)
      (w := fun _ ↦ coproductMapOfHom_fac α gᵢ comm)
      (q := 𝟙 X') (f'' := f') (β := fun _ ↦ PUnit.unit) (q' := coproductι X'ᵢ)
      (w' := coproductInjection_fac X'ᵢ f') g ≪≫
    Pseudofunctor.DescentData.pullFunctorIso (overPseudofunctor S)
      (coproductMapOfHom_left_fac α gᵢ comm) (coproductMapOfHom_right_fac α gᵢ comm) ≪≫
    (Pseudofunctor.DescentData.pullFunctorCompIso (F := overPseudofunctor S)
      (f := fun _ : PUnit.{v + 1} ↦ coproductArrow Xᵢ f PUnit.unit) (p := 𝟙 X)
      (f' := f) (α := fun _ ↦ PUnit.unit) (p' := coproductι Xᵢ)
      (w := coproductInjection_fac Xᵢ f)
      (q := g) (f'' := f') (β := α) (q' := gᵢ) (w' := comm) g).symm

/-- After restricting to the source-family components, the coproduct comparison is the
canonical comparison built from pseudofunctorial composition. -/
noncomputable def coproductComparisonAfterRestrictionOfHom
    (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) :
    ((coproductEquivalence Xᵢ f).functor ⋙
        functor (coproductArrow Xᵢ f PUnit.unit) (coproductArrow X'ᵢ f' PUnit.unit) g
          (coproductMapOfHom α gᵢ) (CommSq.mk (coproductMapOfHom_fac α gᵢ comm))) ⋙
        restrictCoproduct X'ᵢ f' ≅
      (functorOfHom α gᵢ comm ⋙ (coproductEquivalence X'ᵢ f').functor) ⋙
        restrictCoproduct X'ᵢ f' :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (coproductRestrictionIsoOfHom α gᵢ comm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coproductUnitIso Xᵢ f).symm _ ≪≫
    Functor.leftUnitor _ ≪≫
    (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (coproductUnitIso X'ᵢ f') ≪≫
    (Functor.associator _ _ _).symm

/-- Under the coproduct equivalences, family pullback is canonically isomorphic to pullback
along the induced commutative square of coproduct morphisms. -/
noncomputable def coproductIsoOfHom (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) :
    (coproductEquivalence Xᵢ f).functor ⋙
      functor (coproductArrow Xᵢ f PUnit.unit) (coproductArrow X'ᵢ f' PUnit.unit) g
        (coproductMapOfHom α gᵢ) (CommSq.mk (coproductMapOfHom_fac α gᵢ comm)) ≅
      functorOfHom α gᵢ comm ⋙ (coproductEquivalence X'ᵢ f').functor :=
  Functor.fullyFaithfulCancelRight (restrictCoproduct X'ᵢ f')
    (coproductComparisonAfterRestrictionOfHom α gᵢ comm)

/-- Restriction along the source coproduct injections identifies each component of the
coproduct comparison with its canonical pseudofunctorial construction. -/
theorem coproductIsoOfHom_hom_app (α : I' → I) (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i))
    (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) (D : DescentData Xᵢ f) :
    (restrictCoproduct X'ᵢ f').map ((coproductIsoOfHom α gᵢ comm).hom.app D) =
      (coproductComparisonAfterRestrictionOfHom α gᵢ comm).hom.app D := sorry

end Coproduct

end AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback
