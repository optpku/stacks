/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Basic

/-!
# Explicit operations on rational functions of algebraic spaces

Coordinates on the affine line define operations on morphisms and dense-open partial maps.
These operations descend to rational functions, the quotient of partial maps to the affine line.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TypeCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine line over `S`, as a scheme over `S`. -/
def affineLineOver (S : Scheme.{u}) : Over S :=
  Over.mk (𝔸(PUnit.{u + 1}; S) ↘ S)

/-- The affine line `𝔸¹_S`, as an algebraic space over `S`. -/
def affineLine (S : Scheme.{u}) : AlgebraicSpace S :=
  ofOver (affineLineOver S)

/-- The functor of points of `affineLine S` is the Yoneda embedding of the affine line over `S`. -/
theorem affineLine_functorOfPoints (S : Scheme.{u}) :
    (affineLine S).functorOfPoints = yoneda.obj (affineLineOver S) :=
  rfl

/-- The global section of a morphism over `S` into the affine line, extracted from the standard
coordinate. -/
def coordHom {S : Scheme.{u}} {T : Over S} (φ : T ⟶ affineLineOver S) : Γ(T.left, ⊤) :=
  φ.left.appTop (AffineSpace.coord S PUnit.unit)

/-- The morphism over `S` into the affine line classified by a global section. -/
def homOfCoord {S : Scheme.{u}} (T : Over S) (a : Γ(T.left, ⊤)) : T ⟶ affineLineOver S :=
  Over.homMk (AffineSpace.homOfVector T.hom (fun _ : PUnit.{u + 1} ↦ a))
    (AffineSpace.homOfVector_over T.hom (fun _ : PUnit.{u + 1} ↦ a))

/-- Evaluating the morphism associated to a section recovers that section. -/
theorem coordHom_homOfCoord {S : Scheme.{u}} (T : Over S) (a : Γ(T.left, ⊤)) :
    coordHom (homOfCoord T a) = a := by
  exact AffineSpace.homOfVector_appTop_coord _ _ _

/-- The morphism associated to the coordinate of a map to the affine line recovers that map. -/
theorem homOfCoord_coordHom {S : Scheme.{u}} {T : Over S} (φ : T ⟶ affineLineOver S) :
    homOfCoord T (coordHom φ) = φ := by
  apply Over.OverMorphism.ext
  apply AffineSpace.hom_ext
  · exact (AffineSpace.homOfVector_over _ _).trans (Over.w φ).symm
  · intro i
    cases i
    exact AffineSpace.homOfVector_appTop_coord _ _ _

/-- Coordinates pull back along morphisms of schemes over the base. -/
theorem coordHom_comp {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U)
    (g : U ⟶ affineLineOver S) :
    coordHom (f ≫ g) = f.left.appTop (coordHom g) :=
  rfl

/-- The morphism classified by a section commutes with pullback of that section. -/
theorem comp_homOfCoord {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U) (a : Γ(U.left, ⊤)) :
    f ≫ homOfCoord U a = homOfCoord T (f.left.appTop a) := by
  calc
    f ≫ homOfCoord U a = homOfCoord T (coordHom (f ≫ homOfCoord U a)) :=
      (homOfCoord_coordHom _).symm
    _ = homOfCoord T (f.left.appTop a) := by
      rw [coordHom_comp, coordHom_homOfCoord]

variable {S : Scheme.{u}}

/-- Pointwise addition of morphisms into the affine line, induced by addition of coordinates. -/
def homAdd {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) : X ⟶ affineLine S where
  app T := ofHom fun x ↦
    homOfCoord T.unop (coordHom (f.app T x) + coordHom (g.app T x))
  naturality {T U} k := by
    apply ConcreteCategory.hom_ext
    intro x
    change homOfCoord U.unop
      (coordHom (f.app U (X.functorOfPoints.map k x)) +
        coordHom (g.app U (X.functorOfPoints.map k x))) =
      k.unop ≫ homOfCoord T.unop (coordHom (f.app T x) + coordHom (g.app T x))
    have hf : f.app U (X.functorOfPoints.map k x) = k.unop ≫ f.app T x :=
      f.naturality_apply k x
    have hg : g.app U (X.functorOfPoints.map k x) = k.unop ≫ g.app T x :=
      g.naturality_apply k x
    rw [hf, hg, comp_homOfCoord, coordHom_comp, coordHom_comp, map_add]

/-- Pointwise multiplication of morphisms into the affine line, induced by multiplication of
coordinates. -/
def homMul {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) : X ⟶ affineLine S where
  app T := ofHom fun x ↦
    homOfCoord T.unop (coordHom (f.app T x) * coordHom (g.app T x))
  naturality {T U} k := by
    apply ConcreteCategory.hom_ext
    intro x
    change homOfCoord U.unop
      (coordHom (f.app U (X.functorOfPoints.map k x)) *
        coordHom (g.app U (X.functorOfPoints.map k x))) =
      k.unop ≫ homOfCoord T.unop (coordHom (f.app T x) * coordHom (g.app T x))
    have hf : f.app U (X.functorOfPoints.map k x) = k.unop ≫ f.app T x :=
      f.naturality_apply k x
    have hg : g.app U (X.functorOfPoints.map k x) = k.unop ≫ g.app T x :=
      g.naturality_apply k x
    rw [hf, hg, comp_homOfCoord, coordHom_comp, coordHom_comp, map_mul]

/-- The zero morphism into the affine line, classified by the zero section. -/
def homZero (X : AlgebraicSpace S) : X ⟶ affineLine S where
  app T := ofHom fun _ ↦ homOfCoord T.unop 0
  naturality {T U} k := by
    apply ConcreteCategory.hom_ext
    intro x
    change homOfCoord U.unop 0 = k.unop ≫ homOfCoord T.unop 0
    rw [comp_homOfCoord, map_zero]

/-- The unit morphism into the affine line, classified by the unit section. -/
def homOne (X : AlgebraicSpace S) : X ⟶ affineLine S where
  app T := ofHom fun _ ↦ homOfCoord T.unop 1
  naturality {T U} k := by
    apply ConcreteCategory.hom_ext
    intro x
    change homOfCoord U.unop 1 = k.unop ≫ homOfCoord T.unop 1
    rw [comp_homOfCoord, map_one]

/-- Pointwise negation of morphisms into the affine line. -/
def homNeg {X : AlgebraicSpace S} (f : X ⟶ affineLine S) : X ⟶ affineLine S where
  app T := ofHom fun x ↦ homOfCoord T.unop (-coordHom (f.app T x))
  naturality {T U} k := by
    apply ConcreteCategory.hom_ext
    intro x
    change homOfCoord U.unop (-coordHom (f.app U (X.functorOfPoints.map k x))) =
      k.unop ≫ homOfCoord T.unop (-coordHom (f.app T x))
    have hf : f.app U (X.functorOfPoints.map k x) = k.unop ≫ f.app T x :=
      f.naturality_apply k x
    rw [hf, comp_homOfCoord, coordHom_comp, map_neg]

/-- The component of `homAdd` is the morphism classified by the sum of coordinates. -/
theorem homAdd_app {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homAdd f g).app T x = homOfCoord T.unop (coordHom (f.app T x) + coordHom (g.app T x)) :=
  rfl

/-- The component of `homMul` is the morphism classified by the product of coordinates. -/
theorem homMul_app {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homMul f g).app T x = homOfCoord T.unop (coordHom (f.app T x) * coordHom (g.app T x)) :=
  rfl

/-- The component of `homZero` is the morphism classified by the zero section. -/
theorem homZero_app (X : AlgebraicSpace S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homZero X).app T x = homOfCoord T.unop 0 :=
  rfl

/-- The component of `homOne` is the morphism classified by the unit section. -/
theorem homOne_app (X : AlgebraicSpace S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homOne X).app T x = homOfCoord T.unop 1 :=
  rfl

/-- The component of `homNeg` is the morphism classified by the negated coordinate. -/
theorem homNeg_app {X : AlgebraicSpace S} (f : X ⟶ affineLine S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homNeg f).app T x = homOfCoord T.unop (-coordHom (f.app T x)) :=
  rfl

/-- Addition of maps to the affine line commutes with precomposition. -/
theorem comp_homAdd {W X : AlgebraicSpace S} (k : W ⟶ X) (f g : X ⟶ affineLine S) :
    k ≫ homAdd f g = homAdd (k ≫ f) (k ≫ g) :=
  rfl

/-- Multiplication of maps to the affine line commutes with precomposition. -/
theorem comp_homMul {W X : AlgebraicSpace S} (k : W ⟶ X) (f g : X ⟶ affineLine S) :
    k ≫ homMul f g = homMul (k ≫ f) (k ≫ g) :=
  rfl

/-- Negation of maps to the affine line commutes with precomposition. -/
theorem comp_homNeg {W X : AlgebraicSpace S} (k : W ⟶ X) (f : X ⟶ affineLine S) :
    k ≫ homNeg f = homNeg (k ≫ f) :=
  rfl

namespace PartialMap

/-- Addition of partial maps into the affine line, by restricting to the fibre product of the
domains and adding the resulting morphisms. -/
def add {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    PartialMap X (affineLine S) where
  domain := domainInfSite f.domain g.domain
  dense_domain := by
    exact @isDense_domainInfHom S f.domain.left g.domain.left X
      f.domain.hom g.domain.hom (isOpenImmersion_smallZariskiSite f.domain)
      (isOpenImmersion_smallZariskiSite g.domain) f.dense_domain g.dense_domain
  hom := homAdd (domainInfFst f.domain.hom g.domain.hom ≫ f.hom)
      (domainInfSnd f.domain.hom g.domain.hom ≫ g.hom)

/-- Multiplication of partial maps into the affine line, by restricting to the fibre product of
the domains and multiplying the resulting morphisms. -/
def mul {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    PartialMap X (affineLine S) where
  domain := domainInfSite f.domain g.domain
  dense_domain := by
    exact @isDense_domainInfHom S f.domain.left g.domain.left X
      f.domain.hom g.domain.hom (isOpenImmersion_smallZariskiSite f.domain)
      (isOpenImmersion_smallZariskiSite g.domain) f.dense_domain g.dense_domain
  hom := homMul (domainInfFst f.domain.hom g.domain.hom ≫ f.hom)
      (domainInfSnd f.domain.hom g.domain.hom ≫ g.hom)

/-- Negation of a partial map into the affine line. -/
def neg {X : AlgebraicSpace S} (f : PartialMap X (affineLine S)) :
    PartialMap X (affineLine S) where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := homNeg f.hom

private theorem domainInfSite_exists_hom {X : AlgebraicSpace S}
    {W U V : smallZariskiSite X} (a : W ⟶ U) (b : W ⟶ V) :
    ∃ k : W ⟶ domainInfSite U V,
      k.left ≫ domainInfFst U.hom V.hom = a.left ∧
        k.left ≫ domainInfSnd U.hom V.hom = b.left := by
  let w : a.left ≫ U.hom = b.left ≫ V.hom :=
    (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm
  let k := ReasLibPullback.pullbackLift U.hom V.hom a.left b.left w
  have hk₁ : k ≫ domainInfFst U.hom V.hom = a.left :=
    ReasLibPullback.pullbackLift_fst _ _ _ _ _
  have hk₂ : k ≫ domainInfSnd U.hom V.hom = b.left :=
    ReasLibPullback.pullbackLift_snd _ _ _ _ _
  refine ⟨MorphismProperty.Over.homMk k ?_, hk₁, hk₂⟩
  change k ≫ (domainInfFst U.hom V.hom ≫ U.hom) = W.hom
  rw [← Category.assoc, hk₁]
  exact MorphismProperty.Over.w a

private theorem binaryOp_equiv
    (op : ∀ {U : AlgebraicSpace S},
      (U ⟶ affineLine S) → (U ⟶ affineLine S) → (U ⟶ affineLine S))
    (hcomp : ∀ {U V : AlgebraicSpace S} (k : U ⟶ V) (f g : V ⟶ affineLine S),
      k ≫ op f g = op (k ≫ f) (k ≫ g))
    {X : AlgebraicSpace S} {f₁ f₂ g₁ g₂ : PartialMap X (affineLine S)}
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) :
    ∃ (W : smallZariskiSite X) (_ : IsDense W.hom)
      (a : W ⟶ domainInfSite f₁.domain g₁.domain)
      (b : W ⟶ domainInfSite f₂.domain g₂.domain),
      a.left ≫ op (domainInfFst f₁.domain.hom g₁.domain.hom ≫ f₁.hom)
          (domainInfSnd f₁.domain.hom g₁.domain.hom ≫ g₁.hom) =
        b.left ≫ op (domainInfFst f₂.domain.hom g₂.domain.hom ≫ f₂.hom)
          (domainInfSnd f₂.domain.hom g₂.domain.hom ≫ g₂.hom) := by
  obtain ⟨U, hU, uf₁, uf₂, hf⟩ := hf
  obtain ⟨V, hV, vg₁, vg₂, hg⟩ := hg
  change uf₁.left ≫ f₁.hom = uf₂.left ≫ f₂.hom at hf
  change vg₁.left ≫ g₁.hom = vg₂.left ≫ g₂.hom at hg
  let W := domainInfSite U V
  have hW : IsDense W.hom :=
    @isDense_domainInfHom S U.left V.left X U.hom V.hom U.prop V.prop hU hV
  let p : W ⟶ U := MorphismProperty.Over.homMk (domainInfFst U.hom V.hom) rfl
  let q : W ⟶ V := MorphismProperty.Over.homMk (domainInfSnd U.hom V.hom)
    (domainInf_condition U.hom V.hom).symm
  obtain ⟨a, ha₁, ha₂⟩ := domainInfSite_exists_hom (p ≫ uf₁) (q ≫ vg₁)
  obtain ⟨b, hb₁, hb₂⟩ := domainInfSite_exists_hom (p ≫ uf₂) (q ≫ vg₂)
  refine ⟨W, hW, a, b, ?_⟩
  simp only [hcomp, ← Category.assoc, ha₁, ha₂, hb₁, hb₂]
  change op ((p.left ≫ uf₁.left) ≫ f₁.hom) ((q.left ≫ vg₁.left) ≫ g₁.hom) =
    op ((p.left ≫ uf₂.left) ≫ f₂.hom) ((q.left ≫ vg₂.left) ≫ g₂.hom)
  simpa only [Category.assoc] using congrArg₂ (fun f g ↦ op f g)
    (congrArg (fun k ↦ p.left ≫ k) hf) (congrArg (fun k ↦ q.left ≫ k) hg)

/-- Addition of partial maps into the affine line respects equivalence. -/
theorem add_equiv {X : AlgebraicSpace S} {f₁ f₂ g₁ g₂ : PartialMap X (affineLine S)}
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) : (f₁.add g₁).equiv (f₂.add g₂) :=
  binaryOp_equiv (@homAdd S) (@comp_homAdd S) hf hg

/-- Multiplication of partial maps into the affine line respects equivalence. -/
theorem mul_equiv {X : AlgebraicSpace S} {f₁ f₂ g₁ g₂ : PartialMap X (affineLine S)}
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) : (f₁.mul g₁).equiv (f₂.mul g₂) :=
  binaryOp_equiv (@homMul S) (@comp_homMul S) hf hg

/-- Negation of partial maps into the affine line respects equivalence. -/
theorem neg_equiv {X : AlgebraicSpace S} {f g : PartialMap X (affineLine S)} (hf : f.equiv g) :
    f.neg.equiv g.neg := by
  obtain ⟨W, hW, a, b, h⟩ := hf
  refine ⟨W, hW, a, b, ?_⟩
  change a.left ≫ homNeg f.hom = b.left ≫ homNeg g.hom
  rw [comp_homNeg, comp_homNeg]
  exact congrArg homNeg h

end PartialMap

/-- A rational function on an algebraic space `X` over `S` is a rational map from `X` to the
affine line over `S`. -/
abbrev RationalFunction (X : AlgebraicSpace S) :=
  X.RationalMap (affineLine S)

/-- The type of rational functions is the type of rational maps to the affine line. -/
theorem RationalFunction.eq_rationalMap (X : AlgebraicSpace S) :
    RationalFunction X = X.RationalMap (affineLine S) :=
  rfl

/-- Addition of rational functions, by adding dense-open representatives. -/
def RationalFunction.add {X : AlgebraicSpace S} :
    RationalFunction X → RationalFunction X → RationalFunction X :=
  Quotient.lift₂ (fun f g ↦ (f.add g).toRationalMap)
    (fun _ _ _ _ hf hg ↦ Quotient.sound (PartialMap.add_equiv hf hg))

/-- Multiplication of rational functions, by multiplying dense-open representatives. -/
def RationalFunction.mul {X : AlgebraicSpace S} :
    RationalFunction X → RationalFunction X → RationalFunction X :=
  Quotient.lift₂ (fun f g ↦ (f.mul g).toRationalMap)
    (fun _ _ _ _ hf hg ↦ Quotient.sound (PartialMap.mul_equiv hf hg))

/-- Negation of rational functions. -/
def RationalFunction.neg {X : AlgebraicSpace S} : RationalFunction X → RationalFunction X :=
  Quotient.lift (fun f ↦ f.neg.toRationalMap)
    (fun _ _ hf ↦ Quotient.sound (PartialMap.neg_equiv hf))

/-- The zero rational function. -/
def RationalFunction.zero {X : AlgebraicSpace S} : RationalFunction X :=
  (PartialMap.ofHom (homZero X)).toRationalMap

/-- The unit rational function. -/
def RationalFunction.one {X : AlgebraicSpace S} : RationalFunction X :=
  (PartialMap.ofHom (homOne X)).toRationalMap

/-- Addition of rational functions is represented by addition of partial maps on a common dense
open. -/
theorem add_toRationalMap {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    RationalFunction.add f.toRationalMap g.toRationalMap = (f.add g).toRationalMap :=
  rfl

/-- Multiplication of rational functions is represented by multiplication of partial maps on a
common dense open. -/
theorem mul_toRationalMap {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    RationalFunction.mul f.toRationalMap g.toRationalMap = (f.mul g).toRationalMap :=
  rfl

/-- Negation of a rational function is represented on the same dense open domain. -/
theorem neg_toRationalMap {X : AlgebraicSpace S} (f : PartialMap X (affineLine S)) :
    RationalFunction.neg f.toRationalMap = f.neg.toRationalMap :=
  rfl

/-- The zero rational function is represented by the everywhere-defined zero morphism. -/
theorem zero_eq_toRationalMap (X : AlgebraicSpace S) :
    (RationalFunction.zero : RationalFunction X) = (PartialMap.ofHom (homZero X)).toRationalMap :=
  rfl

/-- The unit rational function is represented by the everywhere-defined unit morphism. -/
theorem one_eq_toRationalMap (X : AlgebraicSpace S) :
    (RationalFunction.one : RationalFunction X) = (PartialMap.ofHom (homOne X)).toRationalMap :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
