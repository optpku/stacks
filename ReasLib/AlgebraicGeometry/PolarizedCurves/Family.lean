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
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Polarized families of curves

Objects are proper flat finitely presented scheme families of relative dimension at most 1
equipped with a relatively ample invertible module. Morphisms are cartesian squares together
with an isomorphism of the pulled-back line bundle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- A polarized curve family: a proper flat finite-presentation morphism of relative dimension
at most 1 together with a relatively ample invertible module on the source. -/
def Obj : Type (u + 1) :=
  Σ (X : Scheme.{u}) (S : Scheme.{u}) (hom : X ⟶ S) (line : X.Modules),
    PProd (IsProper hom)
      (PProd (Flat hom)
        (PProd (Scheme.Hom.FinitePresentation hom)
          (PProd (RelativelyAmple hom line)
            (Scheme.Hom.RelativeDimensionLE hom 1))))

/-- The source scheme of a polarized curve family. -/
def Obj.X (P : Obj) : Scheme.{u} := P.fst

/-- The base scheme of a polarized curve family. -/
def Obj.S (P : Obj) : Scheme.{u} := P.snd.fst

/-- The structure morphism of a polarized curve family. -/
def Obj.hom (P : Obj) : P.X ⟶ P.S := P.snd.snd.fst

/-- The relatively ample module of a polarized curve family. -/
def Obj.line (P : Obj) : P.X.Modules := P.snd.snd.snd.fst

/-- The structure morphism of a polarized curve family is proper. -/
theorem Obj.isProper (P : Obj) : IsProper P.hom := P.snd.snd.snd.snd.fst

/-- The structure morphism of a polarized curve family is flat. -/
theorem Obj.isFlat (P : Obj) : Flat P.hom := P.snd.snd.snd.snd.snd.fst

/-- The structure morphism of a polarized curve family is of finite presentation. -/
theorem Obj.finitePresentation (P : Obj) : Scheme.Hom.FinitePresentation P.hom :=
  P.snd.snd.snd.snd.snd.snd.fst

/-- The module of a polarized curve family is relatively ample. -/
theorem Obj.relativelyAmple (P : Obj) : RelativelyAmple P.hom P.line :=
  P.snd.snd.snd.snd.snd.snd.snd.fst

/-- The structure morphism of a polarized curve family has relative dimension at most 1. -/
theorem Obj.relativeDimensionLE (P : Obj) : Scheme.Hom.RelativeDimensionLE P.hom 1 :=
  P.snd.snd.snd.snd.snd.snd.snd.snd

/-- Package a proper flat finite-presentation morphism of relative dimension at most 1 and a
relatively ample module as a polarized curve family. -/
def of {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [RelativelyAmple f L] [Scheme.Hom.RelativeDimensionLE f 1] : Obj :=
  ⟨X, S, f, L, ⟨inferInstance, ⟨inferInstance, ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩⟩⟩⟩

/-- A polarized curve family is a proper flat finite-presentation morphism of relative dimension
at most 1 together with a relatively ample module. -/
theorem Obj.spec (P : Obj) :
    IsProper P.hom ∧ Flat P.hom ∧ Scheme.Hom.FinitePresentation P.hom ∧
      RelativelyAmple P.hom P.line ∧ Scheme.Hom.RelativeDimensionLE P.hom 1 :=
  sorry

/-- A morphism of polarized curve families is a cartesian square of schemes together with an
isomorphism of the pulled-back line bundle. -/
def Hom (x y : Obj) : Type u :=
  Σ (map : x.X ⟶ y.X) (base : x.S ⟶ y.S),
    PProd (IsPullback map x.hom y.hom base)
      ((Scheme.Modules.pullback map).obj y.line ≅ x.line)

/-- The morphism of source schemes of a polarized curve morphism. -/
def Hom.map {x y : Obj} (φ : Hom x y) : x.X ⟶ y.X := φ.fst

/-- The morphism of base schemes of a polarized curve morphism. -/
def Hom.base {x y : Obj} (φ : Hom x y) : x.S ⟶ y.S := φ.snd.fst

/-- The square formed by a polarized curve morphism is cartesian. -/
theorem Hom.isPullback {x y : Obj} (φ : Hom x y) :
    IsPullback φ.map x.hom y.hom φ.base :=
  φ.snd.snd.fst

/-- The line-bundle isomorphism of a polarized curve morphism. -/
def Hom.iso {x y : Obj} (φ : Hom x y) :
    (Scheme.Modules.pullback φ.map).obj y.line ≅ x.line :=
  φ.snd.snd.snd

/-- Build a polarized curve morphism from a cartesian square and a line-bundle isomorphism. -/
def homMk {x y : Obj} (f : x.X ⟶ y.X) (g : x.S ⟶ y.S)
    (h : IsPullback f x.hom y.hom g)
    (φ : (Scheme.Modules.pullback f).obj y.line ≅ x.line) : Hom x y :=
  ⟨f, g, ⟨h, φ⟩⟩

/-- The identity morphism uses identity scheme maps and the identity comparison for pullback of
modules. -/
def Hom.id (x : Obj) : Hom x x :=
  ⟨𝟙 x.X, 𝟙 x.S, ⟨IsPullback.id_horiz x.hom, (Scheme.Modules.pullbackId x.X).app x.line⟩⟩

/-- Composition of polarized curve morphisms is pasting of cartesian squares and composition of
line-bundle isomorphisms. -/
def Hom.comp {x y z : Obj} (α : Hom x y) (β : Hom y z) : Hom x z :=
  ⟨α.map ≫ β.map, α.base ≫ β.base,
    ⟨IsPullback.paste_horiz α.isPullback β.isPullback,
      (Scheme.Modules.pullbackComp α.map β.map).symm.app z.line ≪≫
        (Scheme.Modules.pullback α.map).mapIso β.iso ≪≫ α.iso⟩⟩

/-- Left composition by an identity morphism leaves a polarized curve morphism unchanged. -/
theorem Hom.id_comp {x y : Obj} (α : Hom x y) : Hom.comp (Hom.id x) α = α :=
  sorry

/-- Right composition by an identity morphism leaves a polarized curve morphism unchanged. -/
theorem Hom.comp_id {x y : Obj} (α : Hom x y) : Hom.comp α (Hom.id y) = α :=
  sorry

/-- Composition of polarized curve morphisms is associative. -/
theorem Hom.assoc {w x y z : Obj} (α : Hom w x) (β : Hom x y) (γ : Hom y z) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) :=
  sorry

/-- Polarized curve families and cartesian line-bundle isomorphisms form a category. -/
instance category : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The forgetful functor sending a polarized curve family `(X ⟶ S, L)` to the base scheme `S`. -/
def p : Obj ⥤ Scheme.{u} where
  obj x := x.S
  map φ := Hom.base φ

/-- Schemes as objects of `Over (⊤_ Scheme)`, via the unique map to the terminal scheme. -/
def asOverTerminal : Scheme.{u} ⥤ Over (⊤_ Scheme.{u}) where
  obj X := X.asOver (⊤_ Scheme.{u})
  map f := f.asOver (⊤_ Scheme.{u})
  map_id := sorry
  map_comp := sorry

end AlgebraicGeometry.PolarizedCurves
