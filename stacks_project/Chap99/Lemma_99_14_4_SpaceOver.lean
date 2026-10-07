module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap71.Lemma_71_11_11_Triple
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple
public import stacks_project.Chap99.Lemma_99_13_4_Over
public import stacks_project.Chap99.Situation_99_14_1_Category

/-!
# Polarized algebraic-space families over a fixed algebraic space

The groupoid of pairs `(X ⟶ T, L)` with `X ⟶ T` a proper, flat, finitely
presented morphism of algebraic spaces and `L` relatively ample on `X / T`.
Morphisms are cartesian squares over `𝟙 T` together with an isomorphism of
the pulled-back line bundle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace hiding RelativelyAmple
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- A polarized proper family of algebraic spaces over a fixed algebraic space
`T`: a proper flat finite-presentation morphism `X ⟶ T` together with a
relatively ample module on `X`. -/
structure SpaceOver {S : Scheme.{u}} (T : AlgebraicSpace S) : Type (u + 1) where
  /-- The source algebraic space. -/
  X : AlgebraicSpace S
  /-- The structure morphism. -/
  hom : X ⟶ T
  /-- The relatively ample module on `X`. -/
  line : X.Modules
  /-- The structure morphism is of finite presentation, flat, and proper. -/
  [fpFlatProper : FpFlatProper hom]
  /-- The module is relatively ample on `X / T`. -/
  [relativelyAmple : AlgebraicSpace.RelativelyAmple hom line]

/-- Package a proper flat finite-presentation morphism of algebraic spaces and a
relatively ample module as a polarized family over `T`. -/
def SpaceOver.of {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T) (L : X.Modules)
    [FpFlatProper f] [AlgebraicSpace.RelativelyAmple f L] : SpaceOver T where
  X := X
  hom := f
  line := L

/-- The source of `SpaceOver.of f L` is the supplied algebraic space. -/
theorem SpaceOver.of_X {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    (L : X.Modules) [FpFlatProper f] [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.of f L).X = X :=
  sorry

/-- The structure morphism of `SpaceOver.of f L` is the supplied morphism. -/
theorem SpaceOver.of_hom {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    (L : X.Modules) [FpFlatProper f] [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.of f L).hom = f :=
  sorry

/-- The line bundle of `SpaceOver.of f L` is the supplied module. -/
theorem SpaceOver.of_line {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    (L : X.Modules) [FpFlatProper f] [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.of f L).line = L :=
  sorry

/-- A polarized algebraic-space family over `T` is an `FpFlatProper` morphism
together with a relatively ample module. -/
theorem SpaceOver.spec {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    FpFlatProper P.hom ∧ AlgebraicSpace.RelativelyAmple P.hom P.line :=
  sorry

/-- The structure morphism of a polarized algebraic-space family is of finite
presentation, flat, and proper. -/
instance SpaceOver.instFpFlatProper {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : SpaceOver T) : FpFlatProper P.hom :=
  P.fpFlatProper

/-- The line bundle of a polarized algebraic-space family is relatively ample
on the structure morphism. -/
instance SpaceOver.instRelativelyAmple {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : SpaceOver T) : AlgebraicSpace.RelativelyAmple P.hom P.line :=
  P.relativelyAmple

/-- A morphism of polarized algebraic-space families over `T` is a cartesian
square over `𝟙 T` together with an isomorphism of the pulled-back line bundle. -/
structure SpaceOver.Hom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x y : SpaceOver T) where
  /-- The morphism of source algebraic spaces. -/
  map : x.X ⟶ y.X
  /-- The square formed by `map` over `𝟙 T` is cartesian. -/
  isPullback : IsPullback map x.hom y.hom (𝟙 T)
  /-- The isomorphism `map^* y.line ≅ x.line`. -/
  iso : (AlgebraicSpace.Modules.pullback map).obj y.line ≅ x.line

/-- Build a morphism of polarized algebraic-space families from a cartesian
square over `𝟙 T` and a line-bundle isomorphism. -/
def SpaceOver.homMk {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    SpaceOver.Hom x y where
  map := f
  isPullback := h
  iso := φ

/-- The source map of `SpaceOver.homMk` is the supplied algebraic-space morphism. -/
theorem SpaceOver.homMk_map {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    (SpaceOver.homMk f h φ).map = f :=
  sorry

/-- The line-bundle component of `SpaceOver.homMk` is the supplied isomorphism. -/
theorem SpaceOver.homMk_iso {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    (SpaceOver.homMk f h φ).iso = φ :=
  sorry

/-- A morphism over `T` is a triangle over `T`. -/
theorem SpaceOver.Hom.w {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : α.map ≫ y.hom = x.hom :=
  sorry

/-- A morphism of polarized families over `T` is an isomorphism of source
algebraic spaces. -/
instance SpaceOver.Hom.isIso_map {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (α : SpaceOver.Hom x y) : IsIso α.map :=
  α.isPullback.isIso_fst_of_isIso

/-- The identity morphism uses the identity of the source and the identity
comparison for pullback of modules. -/
def SpaceOver.Hom.id {S : Scheme.{u}} {T : AlgebraicSpace S} (x : SpaceOver T) :
    SpaceOver.Hom x x where
  map := 𝟙 x.X
  isPullback := IsPullback.id_horiz x.hom
  iso := (SmallEtaleModuleGlueing.modulesPullbackId x.X).app x.line

/-- The composite of cartesian squares over `𝟙 T` remains cartesian over `𝟙 T`. -/
theorem SpaceOver.Hom.comp_isPullback {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y z : SpaceOver T} (α : SpaceOver.Hom x y) (β : SpaceOver.Hom y z) :
    IsPullback (α.map ≫ β.map) x.hom z.hom (𝟙 T) :=
  sorry

/-- Composition of morphisms of polarized algebraic-space families is pasting of
cartesian squares and composition of line-bundle isomorphisms. -/
def SpaceOver.Hom.comp {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y z : SpaceOver T} (α : SpaceOver.Hom x y) (β : SpaceOver.Hom y z) :
    SpaceOver.Hom x z where
  map := α.map ≫ β.map
  isPullback := SpaceOver.Hom.comp_isPullback α β
  iso :=
    (AlgebraicSpace.Modules.pullbackCompIso α.map β.map).symm.app z.line ≪≫
      (AlgebraicSpace.Modules.pullback α.map).mapIso β.iso ≪≫ α.iso

/-- Polarized algebraic-space families over `T` and cartesian line-bundle
isomorphisms form a category. -/
instance SpaceOver.category {S : Scheme.{u}} {T : AlgebraicSpace S} :
    Category (SpaceOver T) where
  Hom := SpaceOver.Hom
  id := SpaceOver.Hom.id
  comp := SpaceOver.Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Morphisms of polarized algebraic-space families over `T` are pairs
consisting of a cartesian square over `𝟙 T` and a line-bundle isomorphism. -/
def SpaceOver.homSigma {S : Scheme.{u}} {T : AlgebraicSpace S} (x y : SpaceOver T) :
    (x ⟶ y) ≃
      Σ (f : x.X ⟶ y.X),
        PProd (IsPullback f x.hom y.hom (𝟙 T))
          ((AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) where
  toFun φ := ⟨φ.map, ⟨φ.isPullback, φ.iso⟩⟩
  invFun p := SpaceOver.homMk p.1 p.2.1 p.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Applying `SpaceOver.homSigma` extracts the cartesian square and the
line-bundle isomorphism. -/
theorem SpaceOver.homSigma_apply {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (φ : x ⟶ y) :
    SpaceOver.homSigma x y φ = ⟨φ.map, ⟨φ.isPullback, φ.iso⟩⟩ :=
  sorry

/-- The inverse of `SpaceOver.homSigma` is `SpaceOver.homMk`. -/
theorem SpaceOver.homSigma_symm_apply {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    (SpaceOver.homSigma x y).symm ⟨f, ⟨h, φ⟩⟩ = SpaceOver.homMk f h φ :=
  sorry

/-- The underlying isomorphism of source algebraic spaces of a morphism over
`T`. -/
def SpaceOver.Hom.isoLeft {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (α : SpaceOver.Hom x y) : x.X ≅ y.X :=
  @asIso _ _ x.X y.X α.map (SpaceOver.Hom.isIso_map α)

/-- Forget the line bundle of a polarized algebraic-space family over `T`. -/
def SpaceOver.forget {S : Scheme.{u}} {T : AlgebraicSpace S} :
    SpaceOver T ⥤ FpFlatProperOver T where
  obj P := FpFlatProperOver.mk P.hom
  map {x y} α :=
    ⟨(fpFlatProperOver T).isoMk
      (Over.isoMk (SpaceOver.Hom.isoLeft α) (SpaceOver.Hom.w α))⟩
  map_id := sorry
  map_comp := sorry

/-- `SpaceOver.forget` sends `SpaceOver.of f L` to `FpFlatProperOver.mk f`. -/
theorem SpaceOver.forget_obj {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) (L : X.Modules) [FpFlatProper f]
    [AlgebraicSpace.RelativelyAmple f L] :
    SpaceOver.forget.obj (SpaceOver.of f L) = FpFlatProperOver.mk f :=
  sorry

end AlgebraicGeometry.Polarized
