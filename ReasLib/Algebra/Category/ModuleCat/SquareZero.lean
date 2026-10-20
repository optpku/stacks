module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Modules with a square-zero endomorphism

A module with a square-zero endomorphism is modeled by Mathlib's `HomologicalComplex` for the
reflexive shape on `PUnit`. This file provides the constructor, projection, and morphism API for
that model independently of any particular algebra presenting the endomorphism.

`CategoryTheory.DifferentialObject` instead models a shifted differential
`d : X ⟶ X⟦1⟧`. Using it for an ordinary endomorphism would require choosing an auxiliary
`HasShift (ModuleCat R) (ZMod 1)` instance. The singleton complex records the same mathematics
without adding shift data or making this API depend on a global instance choice.
-/

universe u v

open CategoryTheory

namespace ModuleCat

/-- The category of `R`-modules equipped with a square-zero endomorphism, modeled as
homological complexes for the reflexive shape on a singleton. -/
@[stacks 05CS "square-zero module category"]
abbrev SquareZero.{w, x} (R : Type x) [Ring R] :=
  HomologicalComplex (ModuleCat.{w} R) (ComplexShape.refl PUnit.{1})

namespace SquareZero

variable {R : Type u} [Ring R]

/-- The module carrying a square-zero endomorphism. -/
@[stacks 05CS "square-zero module carrier"]
abbrev carrier (K : ModuleCat.SquareZero.{v} R) : ModuleCat.{v} R :=
  K.X PUnit.unit

/-- The square-zero endomorphism carried by a singleton reflexive complex. -/
@[stacks 05CS "square-zero endomorphism"]
def d (K : ModuleCat.SquareZero.{v} R) : K.carrier ⟶ K.carrier :=
  HomologicalComplex.d K PUnit.unit PUnit.unit

/-- The endomorphism carried by a square-zero module squares to zero. -/
@[simp, stacks 05CS "square-zero relation"]
theorem d_sq (K : ModuleCat.SquareZero.{v} R) : d K ≫ d K = 0 := sorry

/-- The underlying linear endomorphism of a square-zero module squares to zero. -/
@[simp]
theorem d_hom_sq (K : ModuleCat.SquareZero.{v} R) :
    (d K).hom.comp (d K).hom = 0 := sorry

/-- The shape equation used by the singleton square-zero constructor. -/
theorem of_shape (M : ModuleCat.{v} R) (d : M ⟶ M) (i j : PUnit.{1})
    (h : ¬(ComplexShape.refl PUnit.{1}).Rel i j) : d = 0 := sorry

/-- A module with a chosen square-zero endomorphism as a singleton reflexive complex. -/
@[stacks 05CS "square-zero module constructor"]
def of (M : ModuleCat.{v} R) (d : M ⟶ M) (hd : d ≫ d = 0) :
    ModuleCat.SquareZero.{v} R where
  X _ := M
  d _ _ := d
  shape := of_shape M d
  d_comp_d' := fun _ _ _ _ _ ↦ hd

/-- Every component of a singleton square-zero module constructor is the input module. -/
@[simp]
theorem of_X (M : ModuleCat.{v} R) (d : M ⟶ M) (hd : d ≫ d = 0) (i : PUnit.{1}) :
    (of M d hd).X i = M := sorry

/-- The endomorphism of a constructed square-zero module is the chosen endomorphism. -/
@[simp]
theorem d_of (M : ModuleCat.{v} R) (d : M ⟶ M) (hd : d ≫ d = 0) :
    SquareZero.d (of M d hd) = d := sorry

/-- A component map transported from the unique component of each square-zero module. -/
def homMkApp {K L : ModuleCat.SquareZero.{v} R}
    (f : K.carrier ⟶ L.carrier) (i : PUnit.{1}) : K.X i ⟶ L.X i :=
  (K.XIsoOfEq (Subsingleton.elim i PUnit.unit)).hom ≫ f ≫
    (L.XIsoOfEq (Subsingleton.elim PUnit.unit i)).hom

/-- The transported components commute with the square-zero endomorphisms. -/
theorem homMkApp_comm {K L : ModuleCat.SquareZero.{v} R}
    (f : K.carrier ⟶ L.carrier) (hf : f ≫ d L = d K ≫ f)
    (i j : PUnit.{1}) :
    homMkApp f i ≫ HomologicalComplex.d L i j =
      HomologicalComplex.d K i j ≫ homMkApp f j := sorry

/-- A commuting map on the unique components defines a morphism of square-zero modules. -/
@[stacks 05CS "square-zero morphism constructor"]
def homMk {K L : ModuleCat.SquareZero.{v} R}
    (f : K.carrier ⟶ L.carrier) (hf : f ≫ d L = d K ≫ f) : K ⟶ L where
  f := homMkApp f
  comm' := fun i j _ ↦ homMkApp_comm f hf i j

/-- The unique component of a morphism of square-zero modules. -/
@[stacks 05CS "square-zero morphism component"]
def component {K L : ModuleCat.SquareZero.{v} R} (f : K ⟶ L) :
    K.carrier ⟶ L.carrier :=
  f.f PUnit.unit

/-- The unique component of a square-zero morphism commutes with the endomorphisms. -/
theorem component_comm {K L : ModuleCat.SquareZero.{v} R} (f : K ⟶ L) :
    component f ≫ d L = d K ≫ component f := sorry

/-- The square-zero morphism constructor preserves its unique component. -/
@[simp]
theorem component_homMk {K L : ModuleCat.SquareZero.{v} R}
    (f : K.carrier ⟶ L.carrier) (hf : f ≫ d L = d K ≫ f) :
    component (homMk f hf) = f := sorry

/-- Morphisms of singleton square-zero modules are determined by their unique component. -/
@[ext]
theorem hom_ext {K L : ModuleCat.SquareZero.{v} R} {f g : K ⟶ L}
    (h : component f = component g) : f = g := sorry

end SquareZero

end ModuleCat
