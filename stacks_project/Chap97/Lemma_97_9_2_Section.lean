module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Logic.Small.Defs
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Space of sections of an étale morphism onto a finite locally free scheme

A morphism `π : Z ⟶ U` of schemes and a morphism `f : W ⟶ ofOver (Over.mk π)` of
algebraic spaces determine the functor of sections of `W_T ⟶ Z_T` on schemes `T`
over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SpaceOfSections

variable {U Z : Scheme.{u}} {W : AlgebraicSpace U}

/-- The fibre product `Z ×_U T`, viewed as a scheme over `U`. -/
def zOver (π : Z ⟶ U) (T : Over U) : Over U :=
  Over.mk (pullback.fst π T.hom ≫ π)

/-- The projection `Z ×_U T ⟶ Z` over `U`. -/
def zProj (π : Z ⟶ U) (T : Over U) : zOver π T ⟶ Over.mk π :=
  Over.homMk (pullback.fst π T.hom) rfl

/-- The underlying scheme morphism `Z ×_U T' ⟶ Z ×_U T` induced by `h : T' ⟶ T`. -/
def zOverMap_left (π : Z ⟶ U) {T T' : Over U} (h : T' ⟶ T) :
    pullback π T'.hom ⟶ pullback π T.hom :=
  pullback.map π T'.hom π T.hom (𝟙 Z) h.left (𝟙 U)
    ((Category.comp_id π).trans (Category.id_comp π).symm)
    ((Category.comp_id T'.hom).trans (Over.w h).symm)

/-- `zOverMap_left h` commutes with the structure morphisms to `U`. -/
theorem zOverMap_w (π : Z ⟶ U) {T T' : Over U} (h : T' ⟶ T) :
    zOverMap_left π h ≫ (zOver π T).hom = (zOver π T').hom :=
  sorry

/-- The morphism `Z_T' ⟶ Z_T` in `Over U` induced by `h : T' ⟶ T`. -/
def zOverMap (π : Z ⟶ U) {T T' : Over U} (h : T' ⟶ T) : zOver π T' ⟶ zOver π T :=
  Over.homMk (zOverMap_left π h) (zOverMap_w π h)

/-- A section of `W_T ⟶ Z_T` over a scheme `T` over `U`, encoded as a morphism
`σ : ofOver (zOver π T) ⟶ W` over `Z`. -/
structure Point (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) (T : Over U) :
    Type (u + 1) where
  /-- The morphism `σ : Z_T ⟶ W` over `U`. -/
  σ : ofOver (zOver π T) ⟶ W
  /-- `σ` is a section of `f` over `Z`. -/
  is_section : σ ≫ f = ofOverMap (zProj π T)

/-- Build a section from a morphism `σ : Z_T ⟶ W` over `Z`. -/
def Point.of {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (σ : ofOver (zOver π T) ⟶ W) (h : σ ≫ f = ofOverMap (zProj π T)) :
    Point π f T where
  σ := σ
  is_section := h

/-- A point of the space of sections is a section of `W_T ⟶ Z_T`. -/
theorem Point.spec {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (p : Point π f T) : p.σ ≫ f = ofOverMap (zProj π T) :=
  sorry

/-- The functor-of-points element of `W` determined by the section `σ`. -/
def Point.asHom {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (p : Point π f T) : W.functorOfPoints.obj (op (zOver π T)) :=
  yonedaEquiv (p.σ : yoneda.obj (zOver π T) ⟶ W.functorOfPoints)

/-- Restriction of a section along `h : T' ⟶ T` preserves the section equation. -/
theorem Point.restrict_is_section {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)}
    {T T' : Over U} (p : Point π f T) (h : T' ⟶ T) :
    (ofOverMap (zOverMap π h) ≫ p.σ) ≫ f = ofOverMap (zProj π T') :=
  sorry

/-- Restriction of a section along `h : T' ⟶ T`, sending `σ` to `σ ∘ (Z_T' ⟶ Z_T)`. -/
def Point.restrict {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T T' : Over U}
    (p : Point π f T) (h : T' ⟶ T) : Point π f T' where
  σ := ofOverMap (zOverMap π h) ≫ p.σ
  is_section := Point.restrict_is_section p h

/-- The type of sections over a scheme `T` is `u`-small. -/
instance instSmall_point (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) (T : Over U) :
    Small.{u} (Point π f T) :=
  sorry

/-- The functor of sections `F : (Over U)ᵒᵖ ⥤ Type u`. -/
def functor (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) : (Over U)ᵒᵖ ⥤ Type u where
  obj T := Shrink (Point π f T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (Point π f T'.unop)
        (((equivShrink (Point π f T.unop)).symm p).restrict h.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating the functor of sections at `T` gives the shrunk type of sections over `T`. -/
theorem functor_obj (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) (T : Over U) :
    (functor π f).obj (op T) = Shrink (Point π f T) :=
  sorry

/-- The functor of sections acts on a morphism by restriction of sections. -/
theorem functor_map (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    {T T' : (Over U)ᵒᵖ} (h : T ⟶ T') :
    (functor π f).map h =
      TypeCat.ofHom fun p ↦
        equivShrink (Point π f T'.unop)
          (((equivShrink (Point π f T.unop)).symm p).restrict h.unop) :=
  sorry

/-- Values of the functor of sections are equivalent to sections over `T`. -/
def functor_obj_equiv (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) (T : Over U) :
    (functor π f).obj (op T) ≃ Point π f T :=
  (equivShrink (Point π f T)).symm

end AlgebraicGeometry.AlgebraicSpace.SpaceOfSections
