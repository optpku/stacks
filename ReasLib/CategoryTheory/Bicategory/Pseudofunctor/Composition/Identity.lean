module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence

/-!
# Unit coherence for pseudofunctor composition

This leaf provides the left and right unit equivalences for composition of
pseudofunctors.  As with associativity, the object, `1`-morphism, and
`2`-morphism actions agree definitionally, but the pseudofunctor comparison
cells are retained through explicit strong transformations.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]


set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The naturality isomorphism for the left unit comparison of a pseudofunctor. -/
private def idCompStrongTransNaturality
    (F : Pseudofunctor B C) {a b : B} (f : a ⟶ b) :
    ((Pseudofunctor.id B).comp F).map f ≫ 𝟙 (F.obj b) ≅
      𝟙 (((Pseudofunctor.id B).comp F).obj a) ≫ F.map f :=
  (ρ_ (((Pseudofunctor.id B).comp F).map f)) ≪≫ (λ_ (F.map f)).symm

/-- The left unit comparison naturality is compatible with source `2`-cells. -/
private theorem idCompStrongTrans_naturality_naturality
    (F : Pseudofunctor B C) :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      ((Pseudofunctor.id B).comp F).map₂ η ▷ 𝟙 (F.obj b) ≫
          (idCompStrongTransNaturality F g).hom =
        (idCompStrongTransNaturality F f).hom ≫
          𝟙 (((Pseudofunctor.id B).comp F).obj a) ◁ F.map₂ η := sorry

/-- The left unit comparison naturality satisfies the identity coherence equation. -/
private theorem idCompStrongTrans_naturality_id
    (F : Pseudofunctor B C) :
    ∀ a : B,
      (idCompStrongTransNaturality F (𝟙 a)).hom ≫
          𝟙 (((Pseudofunctor.id B).comp F).obj a) ◁ (F.mapId a).hom =
        (((Pseudofunctor.id B).comp F).mapId a).hom ▷ 𝟙 (F.obj a) ≫
          (λ_ (𝟙 (F.obj a))).hom ≫ (ρ_ (𝟙 (F.obj a))).inv := sorry

/-- The left unit comparison naturality satisfies the composition coherence equation. -/
private theorem idCompStrongTrans_naturality_comp
    (F : Pseudofunctor B C) :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (idCompStrongTransNaturality F (f ≫ g)).hom ≫
          𝟙 (((Pseudofunctor.id B).comp F).obj a) ◁ (F.mapComp f g).hom =
        (((Pseudofunctor.id B).comp F).mapComp f g).hom ▷ 𝟙 (F.obj c) ≫
          (α_ _ _ _).hom ≫
            ((Pseudofunctor.id B).comp F).map f ◁
              (idCompStrongTransNaturality F g).hom ≫
              (α_ _ _ _).inv ≫
                (idCompStrongTransNaturality F f).hom ▷ F.map g ≫
                  (α_ _ _ _).hom := sorry

namespace idComp

/-- The strong transformation underlying the left unit equivalence from composition by the
identity pseudofunctor to the original pseudofunctor. -/
def strongTrans (F : Pseudofunctor B C) :
    StrongTrans ((Pseudofunctor.id B).comp F) F where
  app _ := 𝟙 _
  naturality f := idCompStrongTransNaturality F f
  naturality_naturality := idCompStrongTrans_naturality_naturality F
  naturality_id := idCompStrongTrans_naturality_id F
  naturality_comp := idCompStrongTrans_naturality_comp F

/-- Pointwise identity equivalence data for `idComp.strongTrans`. -/
def pointwiseEquivalence (F : Pseudofunctor B C) :
    StrongTrans.PointwiseEquivalence (strongTrans F) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun _ => Bicategory.Equivalence.id _)
    (fun _ ↦ Iso.refl _)

end idComp

/-- Left unit equivalence for pseudofunctor composition. -/
def idComp (F : Pseudofunctor B C) :
    (Pseudofunctor.id B).comp F ≌ F :=
  (idComp.pointwiseEquivalence F).toEquivalence

/-- The naturality isomorphism for the right unit comparison of a pseudofunctor. -/
private def compIdStrongTransNaturality
    (F : Pseudofunctor B C) {a b : B} (f : a ⟶ b) :
    (F.comp (Pseudofunctor.id C)).map f ≫ 𝟙 (F.obj b) ≅
      𝟙 ((F.comp (Pseudofunctor.id C)).obj a) ≫ F.map f :=
  (ρ_ ((F.comp (Pseudofunctor.id C)).map f)) ≪≫ (λ_ (F.map f)).symm

/-- The right unit comparison naturality is compatible with source `2`-cells. -/
private theorem compIdStrongTrans_naturality_naturality
    (F : Pseudofunctor B C) :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      (F.comp (Pseudofunctor.id C)).map₂ η ▷ 𝟙 (F.obj b) ≫
          (compIdStrongTransNaturality F g).hom =
        (compIdStrongTransNaturality F f).hom ≫
          𝟙 ((F.comp (Pseudofunctor.id C)).obj a) ◁ F.map₂ η := sorry

/-- The right unit comparison naturality satisfies the identity coherence equation. -/
private theorem compIdStrongTrans_naturality_id
    (F : Pseudofunctor B C) :
    ∀ a : B,
      (compIdStrongTransNaturality F (𝟙 a)).hom ≫
          𝟙 ((F.comp (Pseudofunctor.id C)).obj a) ◁ (F.mapId a).hom =
        ((F.comp (Pseudofunctor.id C)).mapId a).hom ▷ 𝟙 (F.obj a) ≫
          (λ_ (𝟙 (F.obj a))).hom ≫ (ρ_ (𝟙 (F.obj a))).inv := sorry

/-- The right unit comparison naturality satisfies the composition coherence equation. -/
private theorem compIdStrongTrans_naturality_comp
    (F : Pseudofunctor B C) :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (compIdStrongTransNaturality F (f ≫ g)).hom ≫
          𝟙 ((F.comp (Pseudofunctor.id C)).obj a) ◁ (F.mapComp f g).hom =
        ((F.comp (Pseudofunctor.id C)).mapComp f g).hom ▷ 𝟙 (F.obj c) ≫
          (α_ _ _ _).hom ≫
            (F.comp (Pseudofunctor.id C)).map f ◁
              (compIdStrongTransNaturality F g).hom ≫
              (α_ _ _ _).inv ≫
                (compIdStrongTransNaturality F f).hom ▷ F.map g ≫
                  (α_ _ _ _).hom := sorry

namespace compId

/-- The strong transformation underlying the right unit equivalence from composition by the
identity pseudofunctor to the original pseudofunctor. -/
def strongTrans (F : Pseudofunctor B C) :
    StrongTrans (F.comp (Pseudofunctor.id C)) F where
  app _ := 𝟙 _
  naturality f := compIdStrongTransNaturality F f
  naturality_naturality := compIdStrongTrans_naturality_naturality F
  naturality_id := compIdStrongTrans_naturality_id F
  naturality_comp := compIdStrongTrans_naturality_comp F

/-- Pointwise identity equivalence data for `compId.strongTrans`. -/
def pointwiseEquivalence (F : Pseudofunctor B C) :
    StrongTrans.PointwiseEquivalence (strongTrans F) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun _ => Bicategory.Equivalence.id _)
    (fun _ ↦ Iso.refl _)

end compId

/-- Right unit equivalence for pseudofunctor composition. -/
def compId (F : Pseudofunctor B C) :
    F.comp (Pseudofunctor.id C) ≌ F :=
  (compId.pointwiseEquivalence F).toEquivalence

end Pseudofunctor

end CategoryTheory
