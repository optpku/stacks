/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

/-!
# Families of curves

Objects over a scheme `S` are proper flat finitely presented scheme families of relative
dimension at most 1 with base an object of `Over S`. Morphisms are cartesian squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FiberedCategoryOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- A family of curves over a scheme over `S`: a proper flat finite-presentation morphism of
relative dimension at most 1. -/
def Obj (S : Scheme.{u}) : Type (u + 1) :=
  Σ (base : Over S) (X : Scheme.{u}) (hom : X ⟶ base.left),
    PProd (IsProper hom)
      (PProd (Flat hom)
        (PProd (Scheme.Hom.FinitePresentation hom)
          (Scheme.Hom.RelativeDimensionLE hom 1)))

/-- The base scheme of a family of curves, as an object of `Over S`. -/
def Obj.base {S : Scheme.{u}} (P : Obj S) : Over S := P.fst

/-- The total space of a family of curves. -/
def Obj.X {S : Scheme.{u}} (P : Obj S) : Scheme.{u} := P.snd.fst

/-- The structure morphism of a family of curves. -/
def Obj.hom {S : Scheme.{u}} (P : Obj S) : P.X ⟶ P.base.left := P.snd.snd.fst

/-- The structure morphism of a family of curves is proper. -/
theorem Obj.isProper {S : Scheme.{u}} (P : Obj S) : IsProper P.hom := P.snd.snd.snd.fst

/-- The structure morphism of a family of curves is flat. -/
theorem Obj.isFlat {S : Scheme.{u}} (P : Obj S) : Flat P.hom := P.snd.snd.snd.snd.fst

/-- The structure morphism of a family of curves is of finite presentation. -/
theorem Obj.finitePresentation {S : Scheme.{u}} (P : Obj S) :
    Scheme.Hom.FinitePresentation P.hom :=
  P.snd.snd.snd.snd.snd.fst

/-- The structure morphism of a family of curves has relative dimension at most 1. -/
theorem Obj.relativeDimensionLE {S : Scheme.{u}} (P : Obj S) :
    Scheme.Hom.RelativeDimensionLE P.hom 1 :=
  P.snd.snd.snd.snd.snd.snd

/-- Package a proper flat finite-presentation morphism of relative dimension at most 1 as a
family of curves. -/
def of {S : Scheme.{u}} (base : Over S) (X : Scheme.{u}) (f : X ⟶ base.left)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [Scheme.Hom.RelativeDimensionLE f 1] : Obj S :=
  ⟨base, X, f, ⟨inferInstance, ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩⟩⟩

/-- A family of curves is a proper flat finite-presentation morphism of relative dimension at
most 1. -/
theorem Obj.spec {S : Scheme.{u}} (P : Obj S) :
    IsProper P.hom ∧ Flat P.hom ∧ Scheme.Hom.FinitePresentation P.hom ∧
      Scheme.Hom.RelativeDimensionLE P.hom 1 :=
  sorry

/-- A morphism of curve families is a cartesian square of schemes. -/
def Hom {S : Scheme.{u}} (x y : Obj S) : Type u :=
  Σ (map : x.X ⟶ y.X) (base : x.base ⟶ y.base),
    PLift (IsPullback map x.hom y.hom base.left)

/-- The morphism of total spaces of a morphism of curve families. -/
def Hom.map {S : Scheme.{u}} {x y : Obj S} (φ : Hom x y) : x.X ⟶ y.X := φ.fst

/-- The morphism of bases of a morphism of curve families. -/
def Hom.base {S : Scheme.{u}} {x y : Obj S} (φ : Hom x y) : x.base ⟶ y.base := φ.snd.fst

/-- A morphism of curve families is a cartesian square. -/
theorem Hom.isPullback {S : Scheme.{u}} {x y : Obj S} (φ : Hom x y) :
    IsPullback φ.map x.hom y.hom φ.base.left :=
  φ.snd.snd.down

/-- Build a morphism of curve families from a cartesian square. -/
def homMk {S : Scheme.{u}} {x y : Obj S} (f : x.X ⟶ y.X) (g : x.base ⟶ y.base)
    (h : IsPullback f x.hom y.hom g.left) : Hom x y :=
  ⟨f, g, ⟨h⟩⟩

/-- The identity morphism uses identity scheme maps. -/
def Hom.id {S : Scheme.{u}} (x : Obj S) : Hom x x :=
  ⟨𝟙 x.X, 𝟙 x.base, ⟨IsPullback.id_horiz x.hom⟩⟩

/-- Composition of morphisms of curve families is pasting of cartesian squares. -/
def Hom.comp {S : Scheme.{u}} {x y z : Obj S} (α : Hom x y) (β : Hom y z) : Hom x z :=
  ⟨α.map ≫ β.map, α.base ≫ β.base, ⟨IsPullback.paste_horiz α.isPullback β.isPullback⟩⟩

/-- Left composition by an identity morphism leaves a morphism of curve families unchanged. -/
theorem Hom.id_comp {S : Scheme.{u}} {x y : Obj S} (α : Hom x y) :
    Hom.comp (Hom.id x) α = α :=
  sorry

/-- Right composition by an identity morphism leaves a morphism of curve families unchanged. -/
theorem Hom.comp_id {S : Scheme.{u}} {x y : Obj S} (α : Hom x y) :
    Hom.comp α (Hom.id y) = α :=
  sorry

/-- Composition of morphisms of curve families is associative. -/
theorem Hom.assoc {S : Scheme.{u}} {w x y z : Obj S} (α : Hom w x) (β : Hom x y)
    (γ : Hom y z) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) :=
  sorry

/-- Families of curves and cartesian squares form a category. -/
instance category (S : Scheme.{u}) : Category (Obj S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The forgetful functor sending a family of curves to its base scheme over `S`. -/
def p (S : Scheme.{u}) : Obj S ⥤ Over S where
  obj x := x.base
  map φ := Hom.base φ

/-- The universe-lifted projection of families of curves to `Over S`. -/
def toGroupoidsProjection (S : Scheme.{u}) : ULiftHom.{u + 1} (Obj S) ⥤ Over S :=
  (ULiftHom.down : ULiftHom.{u + 1} (Obj S) ⥤ Obj S) ⋙ p S

/-- The universe-lifted projection of families of curves is fibred in groupoids. -/
instance instIsFiberedInGroupoids (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (toGroupoidsProjection S) :=
  sorry

/-- Families of curves, bundled as a category fibred in groupoids over `Over S` at Hom-universe
`u + 1`. -/
def toGroupoids (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (toGroupoidsProjection S)

/-- The projection of `toGroupoids S` is `toGroupoidsProjection S`. -/
theorem toGroupoids_p (S : Scheme.{u}) :
    (toGroupoids S).p = toGroupoidsProjection S :=
  Groupoids.ofFunctor.p (toGroupoidsProjection S)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
