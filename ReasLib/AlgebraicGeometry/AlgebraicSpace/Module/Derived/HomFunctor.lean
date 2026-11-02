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
# Hom presheaf of derived pullbacks

For any morphism `f : X ⟶ Y` and derived objects `K, E`, the assignment
`V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` is a presheaf on algebraic spaces over `Y`.
The source-facing `homFunctorOver` restricts it to the negative Ext vanishing
subspace `W ⊂ Y`; sheaf and representability results retain their hypotheses.
Scheme versions are obtained by precomposition with `SchemeOver.toOver.op`.
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

/-- The derived Hom presheaf on all algebraic spaces over `Y`.
No geometric or Ext vanishing hypotheses are needed for this construction. -/
def homPresheafOver (f : X ⟶ Y) (K E : ModuleDerived X) :
    (Over Y)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := baseChangePullback f σ.unop.hom K ⟶ baseChangePullback f σ.unop.hom E
  map h := TypeCat.ofHom (baseChangeHom f K E h.unop.left (Over.w h.unop))
  map_id σ := by
    ext u
    exact baseChangeHom_id f K E u
  -- This is the Over-category specialization of `baseChangeHom_comp`.
  map_comp _ _ := by sorry

/-- The values of the general presheaf are morphisms of derived pullbacks. -/
theorem homPresheafOver_obj (f : X ⟶ Y) (K E : ModuleDerived X) (σ : Over Y) :
    (homPresheafOver f K E).obj (op σ) =
      (baseChangePullback f σ.hom K ⟶ baseChangePullback f σ.hom E) := rfl

/-- The general presheaf restricts morphisms using the canonical pullback comparison. -/
theorem homPresheafOver_map (f : X ⟶ Y) (K E : ModuleDerived X)
    {σ τ : Over Y} (h : τ ⟶ σ) :
    (homPresheafOver f K E).map h.op =
      TypeCat.ofHom (baseChangeHom f K E h.left (Over.w h)) := rfl

/-- The derived Hom presheaf on schemes over `Y`. -/
def homPresheaf (f : X ⟶ Y) (K E : ModuleDerived X) :
    (SchemeOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  SchemeOver.toOver.op ⋙ homPresheafOver f K E

/-- Scheme evaluation uses the same derived pullbacks as algebraic-space evaluation. -/
theorem homPresheaf_obj (f : X ⟶ Y) (K E : ModuleDerived X) (σ : SchemeOver Y) :
    (homPresheaf f K E).obj (op σ) =
      (baseChangePullback f σ.hom K ⟶ baseChangePullback f σ.hom E) := rfl

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
def homFunctorOver : (Over (negativeExtVanishing f K E hK hE).X)ᵒᵖ ⥤ Type (u + 1) :=
  (Over.map (negativeExtVanishing f K E hK hE).ι).op ⋙ homPresheafOver f K E

/-- The presheaf on the vanishing open is restriction of the general presheaf
along the open inclusion. -/
theorem homFunctorOver_eq_restriction :
    homFunctorOver f K E hK hE =
      (Over.map (negativeExtVanishing f K E hK hE).ι).op ⋙ homPresheafOver f K E := rfl

/-- Evaluating `homFunctorOver` at an algebraic space over `W` yields derived Hom
of the base-changed complexes. -/
theorem homFunctorOver_obj (σ : Over (negativeExtVanishing f K E hK hE).X) :
    (homFunctorOver f K E hK hE).obj (op σ) =
      (baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) K ⟶
        baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) E) := rfl

/-- `homFunctorOver` acts on morphisms of algebraic spaces over `W` by
`homRestrict`. -/
theorem homFunctorOver_map {σ τ : Over (negativeExtVanishing f K E hK hE).X}
    (h : τ ⟶ σ) :
    (homFunctorOver f K E hK hE).map h.op =
      TypeCat.ofHom (homRestrict f K E hK hE h) := rfl

/-- The restriction of `homFunctorOver` to schemes over `W`. -/
def homFunctor : (SchemeOver (negativeExtVanishing f K E hK hE).X)ᵒᵖ ⥤ Type (u + 1) :=
  SchemeOver.toOver.op ⋙ homFunctorOver f K E hK hE

/-- Evaluating `homFunctor` at a scheme over `W` yields derived Hom of the
base-changed complexes. -/
theorem homFunctor_obj (σ : SchemeOver (negativeExtVanishing f K E hK hE).X) :
    (homFunctor f K E hK hE).obj (op σ) =
      (baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) K ⟶
        baseChangePullback f (σ.hom ≫ (negativeExtVanishing f K E hK hE).ι) E) := rfl

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
