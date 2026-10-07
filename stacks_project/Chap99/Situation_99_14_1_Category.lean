module

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

Objects of `Polarized` are pairs `(X ⟶ S, L)` with `X ⟶ S` proper, flat, and of
finite presentation, and `L` relatively ample on `X / S`. Morphisms are
cartesian squares together with an isomorphism of the pulled-back line bundle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- A polarized proper family: a proper flat finite-presentation morphism of
schemes together with a relatively ample invertible module on the source. -/
structure Obj : Type (u + 1) where
  /-- The source scheme. -/
  X : Scheme.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The structure morphism. -/
  hom : X ⟶ S
  /-- The relatively ample invertible module on `X`. -/
  line : X.Modules
  /-- The structure morphism is proper. -/
  [isProper : IsProper hom]
  /-- The structure morphism is flat. -/
  [isFlat : Flat hom]
  /-- The structure morphism is of finite presentation. -/
  [finitePresentation : Scheme.Hom.FinitePresentation hom]
  /-- The module is relatively ample on `X / S`. -/
  [relativelyAmple : RelativelyAmple hom line]

/-- Package a proper flat finite-presentation morphism and a relatively ample
module as a polarized object. -/
def of {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    Obj where
  X := X
  S := S
  hom := f
  line := L

/-- The source scheme of `of f L` is the supplied source. -/
theorem of_X {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).X = X :=
  sorry

/-- The base scheme of `of f L` is the supplied base. -/
theorem of_S {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).S = S :=
  sorry

/-- The structure morphism of `of f L` is the supplied morphism. -/
theorem of_hom {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).hom = f :=
  sorry

/-- The line bundle of `of f L` is the supplied module. -/
theorem of_line {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] [RelativelyAmple f L] :
    (of f L).line = L :=
  sorry

/-- A polarized object is a proper flat finite-presentation morphism together
with an invertible relatively ample module. -/
theorem Obj.spec (x : Obj) :
    IsProper x.hom ∧ Flat x.hom ∧ Scheme.Hom.FinitePresentation x.hom ∧
      Scheme.Modules.Invertible x.line ∧ RelativelyAmple x.hom x.line :=
  sorry

/-- A morphism of polarized objects is a cartesian square of schemes together
with an isomorphism of the pulled-back line bundle. -/
structure Hom (x y : Obj) where
  /-- The morphism of source schemes. -/
  map : x.X ⟶ y.X
  /-- The morphism of base schemes. -/
  base : x.S ⟶ y.S
  /-- The square formed by `map` and `base` is cartesian. -/
  isPullback : IsPullback map x.hom y.hom base
  /-- The isomorphism `map^* y.line ≅ x.line`. -/
  iso : (Scheme.Modules.pullback map).obj y.line ≅ x.line

/-- Build a polarized morphism from a cartesian square and a line-bundle
isomorphism. -/
def homMk {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) : Hom x y where
  map := f
  base := g
  isPullback := h
  iso := φ

/-- The source map of `homMk` is the supplied scheme morphism. -/
theorem homMk_map {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) :
    (homMk f g h φ).map = f :=
  sorry

/-- The base map of `homMk` is the supplied scheme morphism. -/
theorem homMk_base {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) :
    (homMk f g h φ).base = g :=
  sorry

/-- The line-bundle component of `homMk` is the supplied isomorphism. -/
theorem homMk_iso {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) :
    (homMk f g h φ).iso = φ :=
  sorry

/-- The cartesian square of a morphism identifies the source with the fibre
product of the target morphism along the base map. -/
def Hom.isoFiberProduct {x y : Obj} (φ : Hom x y) :
    x.X ≅ pullback y.hom φ.base :=
  φ.isPullback.isoPullback

/-- The fibre-product comparison commutes with the projection to the target
source. -/
theorem Hom.isoFiberProduct_hom_fst {x y : Obj} (φ : Hom x y) :
    (Hom.isoFiberProduct φ).hom ≫ pullback.fst y.hom φ.base = φ.map :=
  sorry

/-- The identity morphism uses identity scheme maps and the identity comparison
for pullback of modules. -/
def Hom.id (x : Obj) : Hom x x where
  map := 𝟙 x.X
  base := 𝟙 x.S
  isPullback := IsPullback.id_horiz x.hom
  iso := (Scheme.Modules.pullbackId x.X).app x.line

/-- Composition of polarized morphisms is pasting of cartesian squares and
composition of line-bundle isomorphisms. -/
def Hom.comp {x y z : Obj} (α : Hom x y) (β : Hom y z) : Hom x z where
  map := α.map ≫ β.map
  base := α.base ≫ β.base
  isPullback := IsPullback.paste_horiz α.isPullback β.isPullback
  iso :=
    (Scheme.Modules.pullbackComp α.map β.map).symm.app z.line ≪≫
      (Scheme.Modules.pullback α.map).mapIso β.iso ≪≫ α.iso

/-- Polarized objects and cartesian line-bundle isomorphisms form a category. -/
instance category : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Morphisms of polarized objects are triples `(f, g, φ)` consisting of a
cartesian square and a line-bundle isomorphism. -/
def homSigma (x y : Obj) :
    (x ⟶ y) ≃
      Σ (f : x.X ⟶ y.X) (g : x.S ⟶ y.S),
        PProd (IsPullback f x.hom y.hom g)
          ((Scheme.Modules.pullback f).obj y.line ≅ x.line) where
  toFun φ := ⟨φ.map, φ.base, ⟨φ.isPullback, φ.iso⟩⟩
  invFun p := homMk p.1 p.2.1 p.2.2.1 p.2.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Applying `homSigma` extracts the cartesian square and the line-bundle
isomorphism. -/
@[simp]
theorem homSigma_apply {x y : Obj} (φ : x ⟶ y) :
    homSigma x y φ = ⟨φ.map, φ.base, ⟨φ.isPullback, φ.iso⟩⟩ :=
  sorry

/-- The inverse of `homSigma` is `homMk`. -/
@[simp]
theorem homSigma_symm_apply {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) :
    (homSigma x y).symm ⟨f, g, ⟨h, φ⟩⟩ = homMk f g h φ :=
  sorry

/-- The forgetful functor sending a polarized pair `(X ⟶ S, L)` to the base
scheme `S`. -/
def p : Obj ⥤ Scheme.{u} where
  obj x := x.S
  map φ := φ.base

/-- The object part of `p` is the base scheme. -/
theorem p_obj (x : Obj) : p.obj x = x.S :=
  sorry

/-- The morphism part of `p` is the base map of a polarized morphism. -/
theorem p_map {x y : Obj} (φ : x ⟶ y) : p.map φ = φ.base :=
  sorry

/-- Polarized as a category over `Sch_fppf`, via the forgetful functor `p`. -/
def over : BasedCategory.{u, u + 1} Scheme.{u} :=
  BasedCategory.ofFunctor p

/-- The projection of `over` is the forgetful functor `p`. -/
theorem over_p : over.p = p :=
  sorry

end AlgebraicGeometry.Polarized
