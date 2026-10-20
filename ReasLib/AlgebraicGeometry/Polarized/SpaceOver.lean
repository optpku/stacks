module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.Polarized

/-!
# Polarized algebraic-space families over a fixed algebraic space

The groupoid of pairs `(X ⟶ T, L)` with `X ⟶ T` a proper, flat, finitely presented morphism
of algebraic spaces and `L` relatively ample on `X / T`. Morphisms are cartesian squares over
`𝟙 T` together with an isomorphism of the pulled-back line bundle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry hiding QuasiSeparated QuasiCompact LocallyOfFinitePresentation Flat
open AlgebraicGeometry.AlgebraicSpace hiding RelativelyAmple

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- A polarized proper family of algebraic spaces over a fixed algebraic space `T`. -/
def SpaceOver {S : Scheme.{u}} (T : AlgebraicSpace S) : Type (u + 1) :=
  Σ (X : AlgebraicSpace S) (hom : X ⟶ T) (line : X.Modules),
    PProd (AlgebraicSpace.Proper hom)
      (PProd (AlgebraicSpace.Flat hom)
        (PProd (AlgebraicSpace.LocallyOfFinitePresentation hom)
          (PProd (AlgebraicSpace.QuasiCompact hom)
            (PProd (AlgebraicSpace.QuasiSeparated hom) (AlgebraicSpace.RelativelyAmple hom line)))))

/-- The source algebraic space of a polarized family. -/
def SpaceOver.X {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    AlgebraicSpace S :=
  P.1

/-- The structure morphism of a polarized family. -/
def SpaceOver.hom {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    P.X ⟶ T :=
  P.2.1

/-- The relatively ample module of a polarized family. -/
def SpaceOver.line {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    P.X.Modules :=
  P.2.2.1

/-- Package a proper flat finite-presentation morphism of algebraic spaces and a relatively
ample module as a polarized family over `T`. -/
def SpaceOver.of {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] : SpaceOver T :=
  ⟨X, f, L,
    ⟨inferInstance, ⟨inferInstance, ⟨inferInstance, ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩⟩⟩⟩⟩

/-- The source of `SpaceOver.of f L` is the supplied algebraic space. -/
theorem SpaceOver.of_X {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.of f L).X = X :=
  rfl

/-- The structure morphism of `SpaceOver.of f L` is the supplied morphism. -/
theorem SpaceOver.of_hom {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.of f L).hom = f :=
  rfl

/-- The line bundle of `SpaceOver.of f L` is the supplied module. -/
theorem SpaceOver.of_line {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T) (L : X.Modules)
    [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f] [AlgebraicSpace.QuasiCompact f] [AlgebraicSpace.QuasiSeparated f]
    [AlgebraicSpace.RelativelyAmple f L] :
    (SpaceOver.of f L).line = L :=
  rfl

/-- A polarized algebraic-space family over `T` is a proper, flat, finitely presented morphism
together with a relatively ample module. -/
theorem SpaceOver.spec {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    AlgebraicSpace.Proper P.hom ∧ AlgebraicSpace.Flat P.hom ∧ AlgebraicSpace.LocallyOfFinitePresentation P.hom ∧ AlgebraicSpace.QuasiCompact P.hom ∧
      AlgebraicSpace.QuasiSeparated P.hom ∧ AlgebraicSpace.RelativelyAmple P.hom P.line :=
  ⟨P.2.2.2.1, P.2.2.2.2.1, P.2.2.2.2.2.1, P.2.2.2.2.2.2.1, P.2.2.2.2.2.2.2.1, P.2.2.2.2.2.2.2.2⟩

/-- The relatively ample property of a polarized algebraic-space family. -/
def SpaceOver.lineAmple {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    AlgebraicSpace.RelativelyAmple P.hom P.line :=
  (SpaceOver.spec P).2.2.2.2.2

/-- The structure morphism of a polarized family is proper. -/
instance SpaceOver.instProper_hom {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    AlgebraicSpace.Proper P.hom :=
  (SpaceOver.spec P).1

/-- The structure morphism of a polarized family is flat. -/
instance SpaceOver.instFlat_hom {S : Scheme.{u}} {T : AlgebraicSpace S} (P : SpaceOver T) :
    AlgebraicSpace.Flat P.hom :=
  (SpaceOver.spec P).2.1

/-- The structure morphism of a polarized family is locally of finite presentation. -/
instance SpaceOver.instLocallyOfFinitePresentation_hom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : SpaceOver T) : AlgebraicSpace.LocallyOfFinitePresentation P.hom :=
  (SpaceOver.spec P).2.2.1

/-- The structure morphism of a polarized family is quasi-compact. -/
instance SpaceOver.instQuasiCompact_hom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : SpaceOver T) : AlgebraicSpace.QuasiCompact P.hom :=
  (SpaceOver.spec P).2.2.2.1

/-- The structure morphism of a polarized family is quasi-separated. -/
instance SpaceOver.instQuasiSeparated_hom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : SpaceOver T) : AlgebraicSpace.QuasiSeparated P.hom :=
  (SpaceOver.spec P).2.2.2.2.1

/-- The line bundle of a polarized family is relatively ample. -/
instance SpaceOver.instRelativelyAmple_hom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : SpaceOver T) : AlgebraicSpace.RelativelyAmple P.hom P.line :=
  SpaceOver.lineAmple P

/-- A morphism of polarized algebraic-space families over `T` is a cartesian square over `𝟙 T`
together with an isomorphism of the pulled-back line bundle. -/
def SpaceOver.Hom {S : Scheme.{u}} {T : AlgebraicSpace S} (x y : SpaceOver T) :=
  Σ (map : x.X ⟶ y.X),
    PProd (IsPullback map x.hom y.hom (𝟙 T))
      ((AlgebraicSpace.Modules.pullback map).obj y.line ≅ x.line)

/-- The source map of a morphism of polarized families. -/
def SpaceOver.Hom.map {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : x.X ⟶ y.X :=
  α.1

/-- The cartesian square of a morphism of polarized families. -/
theorem SpaceOver.Hom.isPullback {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : IsPullback α.map x.hom y.hom (𝟙 T) :=
  α.2.1

/-- The line-bundle isomorphism of a morphism of polarized families. -/
def SpaceOver.Hom.iso {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) :
    (AlgebraicSpace.Modules.pullback α.map).obj y.line ≅ x.line :=
  α.2.2

/-- Build a morphism of polarized algebraic-space families from a cartesian square over `𝟙 T`
and a line-bundle isomorphism. -/
def SpaceOver.homMk {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    SpaceOver.Hom x y :=
  ⟨f, ⟨h, φ⟩⟩

/-- The source map of `SpaceOver.homMk` is the supplied algebraic-space morphism. -/
theorem SpaceOver.homMk_map {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    (SpaceOver.homMk f h φ).map = f :=
  rfl

/-- The line-bundle component of `SpaceOver.homMk` is the supplied isomorphism. -/
theorem SpaceOver.homMk_iso {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    (SpaceOver.homMk f h φ).iso = φ :=
  rfl

/-- A morphism over `T` is a triangle over `T`. -/
theorem SpaceOver.Hom.w {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : α.map ≫ y.hom = x.hom :=
  α.isPullback.w.trans (Category.comp_id x.hom)

/-- A morphism of polarized families over `T` is an isomorphism of source algebraic spaces. -/
theorem SpaceOver.Hom.isIso_map {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : IsIso α.map :=
  α.isPullback.isIso_fst_of_isIso

/-- The identity morphism uses the identity of the source and the identity comparison for
pullback of modules. -/
def SpaceOver.Hom.id {S : Scheme.{u}} {T : AlgebraicSpace S} (x : SpaceOver T) :
    SpaceOver.Hom x x :=
  SpaceOver.homMk (𝟙 x.X) (IsPullback.id_horiz x.hom)
    ((AlgebraicSpace.Modules.pullbackIdIso x.X).app x.line)

/-- The composite of cartesian squares over `𝟙 T` remains cartesian over `𝟙 T`. -/
theorem SpaceOver.Hom.comp_isPullback {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y z : SpaceOver T} (α : SpaceOver.Hom x y) (β : SpaceOver.Hom y z) :
    IsPullback (α.map ≫ β.map) x.hom z.hom (𝟙 T) := by
  simpa only [Category.comp_id] using α.isPullback.paste_horiz β.isPullback

/-- Composition of morphisms of polarized algebraic-space families is pasting of cartesian
squares and composition of line-bundle isomorphisms. -/
def SpaceOver.Hom.comp {S : Scheme.{u}} {T : AlgebraicSpace S} {x y z : SpaceOver T}
    (α : SpaceOver.Hom x y) (β : SpaceOver.Hom y z) : SpaceOver.Hom x z :=
  SpaceOver.homMk (α.map ≫ β.map) (SpaceOver.Hom.comp_isPullback α β)
    ((AlgebraicSpace.Modules.pullbackCompIso α.map β.map).symm.app z.line ≪≫
      (AlgebraicSpace.Modules.pullback α.map).mapIso β.iso ≪≫ α.iso)

/-- Left unit law for composition of morphisms of polarized families. -/
theorem SpaceOver.Hom.id_comp {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : SpaceOver.Hom.comp (SpaceOver.Hom.id x) α = α :=
  sorry

/-- Right unit law for composition of morphisms of polarized families. -/
theorem SpaceOver.Hom.comp_id {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : SpaceOver.Hom.comp α (SpaceOver.Hom.id y) = α :=
  sorry

/-- Associativity of composition of morphisms of polarized families. -/
theorem SpaceOver.Hom.assoc {S : Scheme.{u}} {T : AlgebraicSpace S} {w x y z : SpaceOver T}
    (α : SpaceOver.Hom w x) (β : SpaceOver.Hom x y) (γ : SpaceOver.Hom y z) :
    SpaceOver.Hom.comp (SpaceOver.Hom.comp α β) γ = SpaceOver.Hom.comp α (SpaceOver.Hom.comp β γ) :=
  sorry

/-- Polarized algebraic-space families over `T` and cartesian line-bundle isomorphisms form a
category. -/
instance SpaceOver.category {S : Scheme.{u}} {T : AlgebraicSpace S} :
    Category (SpaceOver T) where
  Hom := SpaceOver.Hom
  id := SpaceOver.Hom.id
  comp := SpaceOver.Hom.comp
  id_comp := SpaceOver.Hom.id_comp
  comp_id := SpaceOver.Hom.comp_id
  assoc := SpaceOver.Hom.assoc

/-- Morphisms of polarized algebraic-space families over `T` are pairs consisting of a
cartesian square over `𝟙 T` and a line-bundle isomorphism. -/
def SpaceOver.homSigma {S : Scheme.{u}} {T : AlgebraicSpace S} (x y : SpaceOver T) :
    (x ⟶ y) ≃
      Σ (f : x.X ⟶ y.X),
        PProd (IsPullback f x.hom y.hom (𝟙 T))
          ((AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) where
  toFun φ := ⟨φ.map, ⟨φ.isPullback, φ.iso⟩⟩
  invFun p := SpaceOver.homMk p.1 p.2.1 p.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Applying `SpaceOver.homSigma` extracts the cartesian square and the line-bundle
isomorphism. -/
theorem SpaceOver.homSigma_apply {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (φ : x ⟶ y) :
    SpaceOver.homSigma x y φ = ⟨φ.map, ⟨φ.isPullback, φ.iso⟩⟩ :=
  rfl

/-- The inverse of `SpaceOver.homSigma` is `SpaceOver.homMk`. -/
theorem SpaceOver.homSigma_symm_apply {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : SpaceOver T} (f : x.X ⟶ y.X) (h : IsPullback f x.hom y.hom (𝟙 T))
    (φ : (AlgebraicSpace.Modules.pullback f).obj y.line ≅ x.line) :
    (SpaceOver.homSigma x y).symm ⟨f, ⟨h, φ⟩⟩ = SpaceOver.homMk f h φ :=
  rfl

/-- The underlying isomorphism of source algebraic spaces of a morphism over `T`. -/
def SpaceOver.Hom.isoLeft {S : Scheme.{u}} {T : AlgebraicSpace S} {x y : SpaceOver T}
    (α : SpaceOver.Hom x y) : x.X ≅ y.X :=
  @asIso _ _ x.X y.X α.map α.isPullback.isIso_fst_of_isIso

end AlgebraicGeometry.Polarized
