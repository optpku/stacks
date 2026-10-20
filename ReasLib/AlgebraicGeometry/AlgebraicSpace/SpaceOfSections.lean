/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Spaces of sections

Sections of an algebraic-space morphism over a scheme form a contravariant functor.
For an étale morphism onto a finite locally free scheme, this functor is an algebraic
space étale over the base.
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

/-- The scheme morphism `Z ×_U T' ⟶ Z ×_U T` induced by `h : T' ⟶ T`. -/
def zOverMap_left (π : Z ⟶ U) {T T' : Over U} (h : T' ⟶ T) :
    pullback π T'.hom ⟶ pullback π T.hom :=
  pullback.map π T'.hom π T.hom (𝟙 Z) h.left (𝟙 U)
    ((Category.comp_id π).trans (Category.id_comp π).symm)
    ((Category.comp_id T'.hom).trans (Over.w h).symm)

/-- The pullback comparison commutes with the structure morphisms to `U`. -/
theorem zOverMap_w (π : Z ⟶ U) {T T' : Over U} (h : T' ⟶ T) :
    zOverMap_left π h ≫ (zOver π T).hom = (zOver π T').hom :=
  sorry

/-- The morphism `Z_T' ⟶ Z_T` in `Over U` induced by `h : T' ⟶ T`. -/
def zOverMap (π : Z ⟶ U) {T T' : Over U} (h : T' ⟶ T) : zOver π T' ⟶ zOver π T :=
  Over.homMk (zOverMap_left π h) (zOverMap_w π h)

/-- A section of `W_T ⟶ Z_T`, encoded by a point of `W` over `Z_T` whose represented
morphism lies over `Z`. -/
structure Point (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) (T : Over U) : Type u where
  /-- The functor-of-points element corresponding to the morphism `Z_T ⟶ W`. -/
  value : W.functorOfPoints.obj (op (zOver π T))
  /-- The represented morphism is a section over `Z`. -/
  is_section : (yonedaEquiv.symm value : ofOver (zOver π T) ⟶ W) ≫ f =
    SchemeRealization.ofOverMap (zProj π T)

/-- The morphism `Z_T ⟶ W` represented by a section. -/
def Point.σ {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (p : Point π f T) : ofOver (zOver π T) ⟶ W :=
  yonedaEquiv.symm p.value

/-- Construct a section from a morphism `Z_T ⟶ W` over `Z`. -/
def Point.of {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (σ : ofOver (zOver π T) ⟶ W)
    (h : σ ≫ f = SchemeRealization.ofOverMap (zProj π T)) : Point π f T where
  value := yonedaEquiv (σ : yoneda.obj (zOver π T) ⟶ W.functorOfPoints)
  is_section := by
    change (yonedaEquiv.symm (yonedaEquiv σ) : ofOver (zOver π T) ⟶ W) ≫ f = _
    rw [Equiv.symm_apply_apply]
    exact h

/-- The morphism represented by a section lies over `Z`. -/
theorem Point.spec {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (p : Point π f T) : p.σ ≫ f = SchemeRealization.ofOverMap (zProj π T) :=
  p.is_section

/-- The functor-of-points element underlying a section. -/
def Point.asHom {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (p : Point π f T) : W.functorOfPoints.obj (op (zOver π T)) :=
  p.value

/-- Precomposition with the pullback comparison preserves the section equation. -/
theorem Point.restrict_is_section {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)}
    {T T' : Over U} (p : Point π f T) (h : T' ⟶ T) :
    (SchemeRealization.ofOverMap (zOverMap π h) ≫ p.σ) ≫ f =
      SchemeRealization.ofOverMap (zProj π T') :=
  sorry

/-- Restriction of a section along `h : T' ⟶ T` by precomposition with `Z_T' ⟶ Z_T`. -/
def Point.restrict {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T T' : Over U}
    (p : Point π f T) (h : T' ⟶ T) : Point π f T' :=
  Point.of (SchemeRealization.ofOverMap (zOverMap π h) ≫ p.σ)
    (Point.restrict_is_section p h)

/-- Restricting a section along the identity leaves it unchanged. -/
theorem Point.restrict_id {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)} {T : Over U}
    (p : Point π f T) : p.restrict (𝟙 T) = p :=
  sorry

/-- Restriction along a composite agrees with successive restrictions. -/
theorem Point.restrict_comp {π : Z ⟶ U} {f : W ⟶ ofOver (Over.mk π)}
    {T T' T'' : Over U} (p : Point π f T) (h : T' ⟶ T) (h' : T'' ⟶ T') :
    p.restrict (h' ≫ h) = (p.restrict h).restrict h' :=
  sorry

/-- The contravariant functor assigning to `T` over `U` the sections of `W_T ⟶ Z_T`. -/
def functor (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) : (Over U)ᵒᵖ ⥤ Type u where
  obj T := Point π f T.unop
  map h := TypeCat.ofHom fun p ↦ p.restrict h.unop
  map_id := by
    intro T
    ext p
    exact Point.restrict_id p
  map_comp := by
    intro T T' T'' h h'
    ext p
    exact Point.restrict_comp p h.unop h'.unop

/-- Evaluating the section functor at `T` gives the type of sections over `T`. -/
theorem functor_obj (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π)) (T : Over U) :
    (functor π f).obj (op T) = Point π f T :=
  rfl

/-- The section functor acts on morphisms by restriction. -/
theorem functor_map (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    {T T' : (Over U)ᵒᵖ} (h : T ⟶ T') :
    (functor π f).map h = TypeCat.ofHom (fun p ↦ p.restrict h.unop) :=
  rfl

/-- Sections of an étale morphism onto a finite locally free scheme form an algebraic space. -/
instance instIsAlgebraicSpace (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] : IsAlgebraicSpace (functor π f) :=
  sorry

/-- The algebraic space representing sections of an étale morphism onto a finite locally
free scheme. -/
def space (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] : AlgebraicSpace U :=
  ofIsAlgebraicSpace (functor π f)

/-- The functor of points of the section space is the section functor. -/
theorem space_functorOfPoints (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] :
    (space π f).functorOfPoints = functor π f :=
  rfl

/-- The space of sections of an étale morphism onto a finite locally free scheme is étale
over the base. -/
instance instEtale_toBase (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] :
    Etale (SchemeRealization.toBase (space π f)) :=
  sorry

/-- The section functor of an étale morphism onto a finite locally free scheme is an
algebraic space whose structural morphism to the base is étale. -/
theorem isAlgebraicSpace_etale (π : Z ⟶ U) (f : W ⟶ ofOver (Over.mk π))
    [IsFiniteLocallyFree π] [Etale f] :
    IsAlgebraicSpace (functor π f) ∧ Etale (SchemeRealization.toBase (space π f)) :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace.SpaceOfSections
