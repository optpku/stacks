/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Lax
public import ReasLib.CategoryTheory.Bicategory.Comma.Projection.Endpoint

@[expose] public section

/-!
# Lifts into colax comma bicategories

This leaf owns the canonical pseudofunctor induced by an oplax square, together
with its object, morphism, and projection computation API.
-/

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]

namespace ColaxComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

section LiftImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The object of a colax comma bicategory induced by two pseudofunctors and an
oplax comparison between their composites. -/
def liftObj (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    (d : D) : ColaxComma F G where
  left := P.obj d
  right := Q.obj d
  hom := α.app d

/-- The colax comma `1`-morphism induced by the naturality cell of an oplax
comparison. -/
def liftMap (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} (f : d ⟶ e) : liftObj P Q α d ⟶ liftObj P Q α e where
  left := P.map f
  right := Q.map f
  cell := α.naturality f

/-- The comma `2`-morphism induced by naturality of an oplax comparison. -/
def liftMap₂ (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} {f g : d ⟶ e} (η : f ⟶ g) :
    liftMap P Q α f ⟶ liftMap P Q α g where
  left := P.map₂ η
  right := Q.map₂ η
  w := α.naturality_naturality η

/-- The lifted action on `2`-morphisms preserves identities. -/
theorem liftMap₂_id (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} (f : d ⟶ e) :
    liftMap₂ P Q α (𝟙 f) = 𝟙 (liftMap P Q α f) := sorry
/- Proof strategy: apply comma `2`-morphism extensionality and use `P.map₂_id` and `Q.map₂_id`
on the endpoint components. -/

/-- The lifted action on `2`-morphisms preserves vertical composition. -/
theorem liftMap₂_comp (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} {f g h : d ⟶ e} (η : f ⟶ g) (θ : g ⟶ h) :
    liftMap₂ P Q α (η ≫ θ) =
      liftMap₂ P Q α η ≫ liftMap₂ P Q α θ := sorry
/- Proof strategy: apply comma `2`-morphism extensionality; the two endpoint equations are
`P.map₂_comp` and `Q.map₂_comp`. -/

namespace Implementation

/- Implementation boundary: the prelax packaging, comparison isomorphisms, and pseudofunctor
coherence are private. The public lift owner retains semantic obj, map, and map₂ facades. -/

/-- The underlying prelax functor of the canonical factorization through a
colax comma bicategory. -/
private def liftPrelax (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax)) :
    PrelaxFunctor D (ColaxComma F G) where
  obj := liftObj P Q α
  map := liftMap P Q α
  map₂ := liftMap₂ P Q α
  map₂_id := liftMap₂_id P Q α
  map₂_comp := liftMap₂_comp P Q α

/-- Compatibility needed to lift the two identity comparisons into the comma
hom-category. -/
private theorem liftMapId_w (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax)) (d : D) :
    (F.map₂ (P.mapId d).hom ▷ α.app d) ≫
        ((𝟙 (liftObj P Q α d)) : liftObj P Q α d ⟶ liftObj P Q α d).cell =
      α.naturality (𝟙 d) ≫
        (α.app d ◁ G.map₂ (Q.mapId d).hom) := sorry
/- Proof strategy: normalize the canonical comma identity cell and rewrite with `α.naturality_id`; cancel the
remaining factors using the identity coherences of `P`, `Q`, `F`, and `G`. -/

/-- The identity comparison of the canonical comma factorization. -/
private def liftMapId (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax)) (d : D) :
    (liftPrelax P Q α).map (𝟙 d) ≅ 𝟙 (liftObj P Q α d) :=
  isoMk (P.mapId d) (Q.mapId d) (liftMapId_w P Q α d)

/-- Compatibility needed to lift the two composition comparisons into the
comma hom-category. -/
private theorem liftMapComp_w (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e k : D} (f : d ⟶ e) (g : e ⟶ k) :
    (F.map₂ (P.mapComp f g).hom ▷ α.app k) ≫
        ((liftMap P Q α f) ≫ liftMap P Q α g).cell =
      α.naturality (f ≫ g) ≫
        (α.app d ◁ G.map₂ (Q.mapComp f g).hom) := sorry
/- Proof strategy: normalize the canonical comma composite cell, use `α.naturality_comp` for the central pasting, and rewrite
the boundary with the composition coherences of `P`, `Q`, `F`, and `G`. -/

/-- The composition comparison of the canonical comma factorization. -/
private def liftMapComp (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e k : D} (f : d ⟶ e) (g : e ⟶ k) :
    (liftPrelax P Q α).map (f ≫ g) ≅
      (liftPrelax P Q α).map f ≫ (liftPrelax P Q α).map g :=
  isoMk (P.mapComp f g) (Q.mapComp f g) (liftMapComp_w P Q α f g)

/-- Left-whiskering coherence for the canonical comma factorization. -/
private theorem liftMap₂_whiskerLeft (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e k : D} (f : d ⟶ e) {g h : e ⟶ k} (η : g ⟶ h) :
    (liftPrelax P Q α).map₂ (f ◁ η) =
      (liftMapComp P Q α f g).hom ≫
        (liftPrelax P Q α).map f ◁ (liftPrelax P Q α).map₂ η ≫
          (liftMapComp P Q α f h).inv := sorry
/- Proof strategy: apply comma `2`-morphism extensionality; the endpoint equations are the
left-whiskering coherence axioms of `P` and `Q`. -/

/-- Right-whiskering coherence for the canonical comma factorization. -/
private theorem liftMap₂_whiskerRight (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e k : D} {f g : d ⟶ e} (η : f ⟶ g) (h : e ⟶ k) :
    (liftPrelax P Q α).map₂ (η ▷ h) =
      (liftMapComp P Q α f h).hom ≫
        (liftPrelax P Q α).map₂ η ▷ (liftPrelax P Q α).map h ≫
          (liftMapComp P Q α g h).inv := sorry
/- Proof strategy: apply comma `2`-morphism extensionality; use the right-whiskering coherence
axioms of `P` and `Q` on the endpoint components. -/

/-- Associator coherence for the canonical comma factorization. -/
private theorem liftMap₂_associator (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e k l : D} (f : d ⟶ e) (g : e ⟶ k) (h : k ⟶ l) :
    (liftPrelax P Q α).map₂ (α_ f g h).hom =
      (liftMapComp P Q α (f ≫ g) h).hom ≫
        (liftMapComp P Q α f g).hom ▷ (liftPrelax P Q α).map h ≫
          (α_ ((liftPrelax P Q α).map f) ((liftPrelax P Q α).map g)
            ((liftPrelax P Q α).map h)).hom ≫
            (liftPrelax P Q α).map f ◁ (liftMapComp P Q α g h).inv ≫
              (liftMapComp P Q α f (g ≫ h)).inv := sorry
/- Proof strategy: apply comma `2`-morphism extensionality; the two endpoint equations are
precisely the associator coherence axioms of `P` and `Q`. -/

/-- Left-unitor coherence for the canonical comma factorization. -/
private theorem liftMap₂_leftUnitor (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} (f : d ⟶ e) :
    (liftPrelax P Q α).map₂ (λ_ f).hom =
      (liftMapComp P Q α (𝟙 d) f).hom ≫
        (liftMapId P Q α d).hom ▷ (liftPrelax P Q α).map f ≫
          (λ_ ((liftPrelax P Q α).map f)).hom := sorry
/- Proof strategy: apply comma `2`-morphism extensionality; reduce the endpoints to the left-unitor
coherence axioms of `P` and `Q`. -/

/-- Right-unitor coherence for the canonical comma factorization. -/
private theorem liftMap₂_rightUnitor (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} (f : d ⟶ e) :
    (liftPrelax P Q α).map₂ (ρ_ f).hom =
      (liftMapComp P Q α f (𝟙 e)).hom ≫
        (liftPrelax P Q α).map f ◁ (liftMapId P Q α e).hom ≫
          (ρ_ ((liftPrelax P Q α).map f)).hom := sorry
/- Proof strategy: apply comma `2`-morphism extensionality; reduce the endpoints to the
right-unitor coherence axioms of `P` and `Q`. -/

end Implementation

/-- The canonical pseudofunctor factoring an oplax square through the colax
comma bicategory. -/
def lift (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax)) :
    D ⥤ᵖ ColaxComma F G where
  toPrelaxFunctor := Implementation.liftPrelax P Q α
  mapId := Implementation.liftMapId P Q α
  mapComp := Implementation.liftMapComp P Q α
  map₂_whisker_left := Implementation.liftMap₂_whiskerLeft P Q α
  map₂_whisker_right := Implementation.liftMap₂_whiskerRight P Q α
  map₂_associator := Implementation.liftMap₂_associator P Q α
  map₂_left_unitor := Implementation.liftMap₂_leftUnitor P Q α
  map₂_right_unitor := Implementation.liftMap₂_rightUnitor P Q α

/-- The canonical comma lift has the explicit lifted comma object at each source object. -/
@[simp]
theorem lift_obj (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax)) (d : D) :
    (lift P Q α).obj d = liftObj P Q α d := sorry
/- Proof strategy: unfold lift and project the object field of its private prelax core. -/

/-- The canonical comma lift maps a 1-morphism by the explicit lifted comma morphism. -/
@[simp]
theorem lift_map (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} (f : d ⟶ e) :
    (lift P Q α).map f = liftMap P Q α f := sorry
/- Proof strategy: unfold lift and project the map field of its private prelax core. -/

/-- The canonical comma lift maps a 2-morphism by the explicit lifted comma 2-morphism. -/
@[simp]
theorem lift_map₂ (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax))
    {d e : D} {f g : d ⟶ e} (η : f ⟶ g) :
    (lift P Q α).map₂ η = liftMap₂ P Q α η := sorry
/- Proof strategy: unfold lift and project the 2-morphism map of its private prelax core. -/

/-- The left projection of the canonical comma factorization recovers `P`. -/
theorem lift_fst (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax)) :
    (lift P Q α).comp (fst F G) = P := sorry
/- Proof strategy: use pseudofunctor extensionality; object, map, and `2`-map projections of `lift`
are definitionally the corresponding fields of `P`. -/

/-- The right projection of the canonical comma factorization recovers `Q`. -/
theorem lift_snd (P : D ⥤ᵖ A) (Q : D ⥤ᵖ B)
    (α : Lax.OplaxTrans ((P.comp F).toLax) ((Q.comp G).toLax)) :
    (lift P Q α).comp (snd F G) = Q := sorry
/- Proof strategy: use pseudofunctor extensionality; the right endpoint projections of `lift` are
definitionally the object, map, and `2`-map data of `Q`. -/

end LiftImplementation

end ColaxComma
end Bicategory
end CategoryTheory
