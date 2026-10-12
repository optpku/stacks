/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# The category of polarized proper schemes

Objects of Polarized are pairs `(X ⟶ S, L)` with `X ⟶ S` proper, flat, and of finite
presentation, and `L` relatively ample on `X / S`. Morphisms are cartesian squares together
with an isomorphism of the pulled-back line bundle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The terminal scheme `Spec ℤ` in universe `u`. -/
abbrev specZ : Scheme.{u} :=
  Spec (.of (ULift.{u} ℤ))

/-- A polarized proper family: a proper flat finite-presentation morphism of schemes together
with a relatively ample invertible module on the source. -/
def Obj : Type (u + 1) :=
  Σ (X : Scheme.{u}) (S : Scheme.{u}) (hom : X ⟶ S) (line : X.Modules),
    PProd (IsProper hom)
      (PProd (Flat hom)
        (PProd (Scheme.Hom.FinitePresentation hom) (RelativelyAmple hom line)))

/-- The source scheme of a polarized object. -/
def Obj.X (x : Obj) : Scheme.{u} := x.1

/-- The base scheme of a polarized object. -/
def Obj.S (x : Obj) : Scheme.{u} := x.2.1

/-- The structure morphism of a polarized object. -/
def Obj.hom (x : Obj) : x.X ⟶ x.S := x.2.2.1

/-- The relatively ample module of a polarized object. -/
def Obj.line (x : Obj) : x.X.Modules := x.2.2.2.1

/-- Package a proper flat finite-presentation morphism and a relatively ample module as a
polarized object. -/
def of {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] : Obj :=
  ⟨X, S, f, L, ⟨inferInstance, ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩⟩⟩

/-- The source scheme of `of f L` is the supplied source. -/
theorem of_X {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).X = X :=
  rfl

/-- The base scheme of `of f L` is the supplied base. -/
theorem of_S {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).S = S :=
  rfl

/-- The structure morphism of `of f L` is the supplied morphism. -/
theorem of_hom {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).hom = f :=
  rfl

/-- The line bundle of `of f L` is the supplied module. -/
theorem of_line {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).line = L :=
  rfl

/-- A morphism of polarized objects is a cartesian square of schemes together with an
isomorphism of the pulled-back line bundle. -/
def Hom (x y : Obj) :=
  Σ (map : x.X ⟶ y.X) (base : x.S ⟶ y.S),
    PProd (IsPullback map x.hom y.hom base)
      ((Scheme.Modules.pullback map).obj y.line ≅ x.line)

/-- The source map of a polarized morphism. -/
def Hom.map {x y : Obj} (φ : Hom x y) : x.X ⟶ y.X := φ.1

/-- The base map of a polarized morphism. -/
def Hom.base {x y : Obj} (φ : Hom x y) : x.S ⟶ y.S := φ.2.1

/-- The cartesian square of a polarized morphism. -/
theorem Hom.isPullback {x y : Obj} (φ : Hom x y) :
    IsPullback φ.map x.hom y.hom φ.base :=
  φ.2.2.1

/-- The line-bundle isomorphism of a polarized morphism. -/
def Hom.iso {x y : Obj} (φ : Hom x y) :
    (Scheme.Modules.pullback φ.map).obj y.line ≅ x.line :=
  φ.2.2.2

/-- Build a polarized morphism from a cartesian square and a line-bundle isomorphism. -/
def homMk {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) : Hom x y :=
  ⟨f, g, ⟨h, φ⟩⟩

/-- The source map of `homMk` is the supplied scheme morphism. -/
theorem homMk_map {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) :
    (homMk f g h φ).map = f :=
  rfl

/-- The base map of `homMk` is the supplied scheme morphism. -/
theorem homMk_base {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) :
    (homMk f g h φ).base = g :=
  rfl

/-- The line-bundle component of `homMk` is the supplied isomorphism. -/
theorem homMk_iso {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) :
    (homMk f g h φ).iso = φ :=
  rfl

/-- The identity morphism uses identity scheme maps and the identity comparison for pullback
of modules. -/
def Hom.id (x : Obj) : Hom x x :=
  homMk (𝟙 x.X) (𝟙 x.S) (IsPullback.id_horiz x.hom) ((Scheme.Modules.pullbackId x.X).app x.line)

/-- Composition of polarized morphisms is pasting of cartesian squares and composition of
line-bundle isomorphisms. -/
def Hom.comp {x y z : Obj} (α : Hom x y) (β : Hom y z) : Hom x z :=
  homMk (α.map ≫ β.map) (α.base ≫ β.base) (IsPullback.paste_horiz α.isPullback β.isPullback)
    ((Scheme.Modules.pullbackComp α.map β.map).symm.app z.line ≪≫
      (Scheme.Modules.pullback α.map).mapIso β.iso ≪≫ α.iso)

/-- Left unit law for composition of polarized morphisms. -/
theorem Hom.id_comp {x y : Obj} (α : Hom x y) : Hom.comp (Hom.id x) α = α :=
  sorry

/-- Right unit law for composition of polarized morphisms. -/
theorem Hom.comp_id {x y : Obj} (α : Hom x y) : Hom.comp α (Hom.id y) = α :=
  sorry

/-- Associativity of composition of polarized morphisms. -/
theorem Hom.assoc {w x y z : Obj} (α : Hom w x) (β : Hom x y) (γ : Hom y z) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) :=
  sorry

/-- Polarized objects and cartesian line-bundle isomorphisms form a category. -/
instance category : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The forgetful functor sending a polarized pair `(X ⟶ S, L)` to the base scheme `S`. -/
def p : Obj ⥤ Scheme.{u} where
  obj x := x.S
  map φ := φ.base

/-- Identity morphisms are sent to identity morphisms in `Sch / Spec ℤ`. -/
theorem schemeToOverSpecZ_map_id (T : Scheme.{u}) :
    (Over.homMk (𝟙 T) (specULiftZIsTerminal.hom_ext _ _) :
        Over.mk (specULiftZIsTerminal.from T) ⟶ Over.mk (specULiftZIsTerminal.from T)) =
      𝟙 (Over.mk (specULiftZIsTerminal.from T)) :=
  sorry

/-- Composition of scheme morphisms is preserved in `Sch / Spec ℤ`. -/
theorem schemeToOverSpecZ_map_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Over.homMk (f ≫ g) (specULiftZIsTerminal.hom_ext _ _) :
        Over.mk (specULiftZIsTerminal.from X) ⟶ Over.mk (specULiftZIsTerminal.from Z)) =
      (Over.homMk f (specULiftZIsTerminal.hom_ext _ _) :
          Over.mk (specULiftZIsTerminal.from X) ⟶ Over.mk (specULiftZIsTerminal.from Y)) ≫
        (Over.homMk g (specULiftZIsTerminal.hom_ext _ _) :
          Over.mk (specULiftZIsTerminal.from Y) ⟶ Over.mk (specULiftZIsTerminal.from Z)) :=
  sorry

/-- The functor sending a scheme to itself as an object of `Sch / Spec ℤ`. -/
def schemeToOverSpecZ : Scheme.{u} ⥤ Over specZ.{u} where
  obj T := Over.mk (specULiftZIsTerminal.from T)
  map f := Over.homMk f (specULiftZIsTerminal.hom_ext _ _)
  map_id := schemeToOverSpecZ_map_id
  map_comp := schemeToOverSpecZ_map_comp

/-- Polarized as a category over `(Sch / Spec ℤ)_fppf`, via the forgetful functor `p` followed
by the identification of schemes with objects of `Sch / Spec ℤ`. -/
abbrev overSpecZ : BasedCategory.{u, u + 1} (Over specZ.{u}) :=
  BasedCategory.ofFunctor (p ⋙ schemeToOverSpecZ)

/-- The projection of `overSpecZ` is `p ⋙ schemeToOverSpecZ`. -/
theorem overSpecZ_p : overSpecZ.p = p ⋙ schemeToOverSpecZ :=
  rfl

end AlgebraicGeometry.Polarized
