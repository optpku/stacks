/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.NegativeExt

/-!
# Hom functor of derived pullbacks over the vanishing locus

On algebraic spaces over the negative Ext vanishing subspace `W ⊂ Y`, the
assignment `V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` is a contravariant functor. Its
restriction to schemes over `W` is the comparison target of
`IsAffineFinitePresentationOver`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

variable {X Y : AlgebraicSpace S}

/-- Restriction of a derived Hom after base change along a morphism of algebraic
spaces over `Y`. -/
def baseChangeHom (f : X ⟶ Y) (K E : ModuleDerived X) {V V' : AlgebraicSpace S}
    {g : V ⟶ Y} {g' : V' ⟶ Y} (φ : V' ⟶ V) (hφ : φ ≫ g = g')
    (u : baseChangePullback f g K ⟶ baseChangePullback f g E) :
    baseChangePullback f g' K ⟶ baseChangePullback f g' E :=
  (baseChangePullbackRestrict f φ hφ K).hom ≫
    (pullback (baseChangeSpaceMap f φ hφ)).map u ≫
      (baseChangePullbackRestrict f φ hφ E).inv

/-- Restriction of derived Hom along the identity morphism over `Y` is the
identity. -/
theorem baseChangeHom_id (f : X ⟶ Y) (K E : ModuleDerived X)
    {V : AlgebraicSpace S} {g : V ⟶ Y}
    (u : baseChangePullback f g K ⟶ baseChangePullback f g E) :
    baseChangeHom f K E (𝟙 V) (Category.id_comp g) u = u := sorry

/-- Restriction of derived Hom along a composite morphism over `Y` is the
composite restriction. -/
theorem baseChangeHom_comp (f : X ⟶ Y) (K E : ModuleDerived X)
    {V V' V'' : AlgebraicSpace S} {g : V ⟶ Y} {g' : V' ⟶ Y} {g'' : V'' ⟶ Y}
    (φ : V' ⟶ V) (hφ : φ ≫ g = g') (ψ : V'' ⟶ V') (hψ : ψ ≫ g' = g'')
    (u : baseChangePullback f g K ⟶ baseChangePullback f g E) :
    baseChangeHom f K E (ψ ≫ φ)
      ((Category.assoc ψ φ g).trans
        ((congrArg (fun k ↦ ψ ≫ k) hφ).trans hψ)) u =
      baseChangeHom f K E ψ hψ (baseChangeHom f K E φ hφ u) := sorry

variable (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
variable (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
variable (hE : IsPerfectRelativeTo f E)

/-- Restriction of derived Hom along a morphism of algebraic spaces over `W`. -/
def homRestrict {σ τ : Over (negativeExtVanishing f K E hK hE).X} (h : τ ⟶ σ)
    (u : baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) K ⟶
      baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) E) :
    baseChangePullback f (τ.hom ≫ (negativeExtVanishing f K E hK hE).ι) K ⟶
      baseChangePullback f (τ.hom ≫ (negativeExtVanishing f K E hK hE).ι) E :=
  baseChangeHom f K E h.left
    ((Category.assoc h.left σ.hom (negativeExtVanishing f K E hK hE).ι).symm.trans
      (congrArg (fun k ↦ k ≫ (negativeExtVanishing f K E hK hE).ι) (Over.w h)))
    u

/-- Derived Hom restriction over the vanishing open preserves identity morphisms. -/
theorem homRestrict_id (σ : Over (negativeExtVanishing f K E hK hE).X) :
    TypeCat.ofHom (homRestrict f K E hK hE (𝟙 σ)) = 𝟙 _ := sorry

/-- Derived Hom restriction over the vanishing open reverses composition. -/
theorem homRestrict_comp {σ τ υ : Over (negativeExtVanishing f K E hK hE).X}
    (h : τ ⟶ σ) (g : υ ⟶ τ) :
    TypeCat.ofHom (homRestrict f K E hK hE (g ≫ h)) =
      TypeCat.ofHom (homRestrict f K E hK hE h) ≫
        TypeCat.ofHom (homRestrict f K E hK hE g) := sorry

/-- The functor `V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` on algebraic spaces over `W`. -/
def homFunctorOver : (Over (negativeExtVanishing f K E hK hE).X)ᵒᵖ ⥤ Type (u + 1) where
  obj σ :=
    baseChangePullback f (σ.unop.hom ≫ (negativeExtVanishing f K E hK hE).ι) K ⟶
      baseChangePullback f (σ.unop.hom ≫ (negativeExtVanishing f K E hK hE).ι) E
  map {σ τ} h := TypeCat.ofHom (homRestrict f K E hK hE h.unop)
  map_id σ := homRestrict_id f K E hK hE σ.unop
  map_comp h g := homRestrict_comp f K E hK hE h.unop g.unop

/-- Evaluating `homFunctorOver` at an algebraic space over `W` yields derived Hom
of the base-changed complexes. -/
theorem homFunctorOver_obj (σ : Over (negativeExtVanishing f K E hK hE).X) :
    (homFunctorOver f K E hK hE).obj (op σ) =
      (baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) K ⟶
        baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) E) := sorry

/-- `homFunctorOver` acts on morphisms of algebraic spaces over `W` by
`homRestrict`. -/
theorem homFunctorOver_map {σ τ : Over (negativeExtVanishing f K E hK hE).X}
    (h : τ ⟶ σ) :
    (homFunctorOver f K E hK hE).map h.op =
      TypeCat.ofHom (homRestrict f K E hK hE h) := sorry

/-- The restriction of `homFunctorOver` to schemes over `W`. -/
def homFunctor : (SchemeOver (negativeExtVanishing f K E hK hE).X)ᵒᵖ ⥤ Type (u + 1) :=
  SchemeOver.toOver.op ⋙ homFunctorOver f K E hK hE

/-- Evaluating `homFunctor` at a scheme over `W` yields derived Hom of the
base-changed complexes. -/
theorem homFunctor_obj (σ : SchemeOver (negativeExtVanishing f K E hK hE).X) :
    (homFunctor f K E hK hE).obj (op σ) =
      (baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) K ⟶
        baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) E) := sorry

/-- The derived Hom presheaf over the negative Ext vanishing open is an fppf sheaf. -/
theorem homFunctorOver_isSheaf :
    Presheaf.IsSheaf
      ((AlgebraicGeometry.AlgebraicSpace.fppfTopology S).over
        (negativeExtVanishing f K E hK hE).X)
      (homFunctorOver f K E hK hE) := sorry

/-- The functor `V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` on algebraic
spaces over `W` is represented by an algebraic space affine of finite
presentation over `W`. -/
theorem homFunctorOver_isAffineFinitePresentation :
    ∃ (F : AlgebraicSpace S) (π : F ⟶ (negativeExtVanishing f K E hK hE).X),
      Affine π ∧ FinitePresentation π ∧
        Nonempty (homFunctorOver f K E hK hE ≅ yoneda.obj (Over.mk π)) := sorry

/-- The scheme-level Hom functor is represented by an algebraic space affine of
finite presentation over `W`. -/
theorem homFunctor_isAffineFinitePresentation :
    IsAffineFinitePresentationOver (homFunctor f K E hK hE) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
