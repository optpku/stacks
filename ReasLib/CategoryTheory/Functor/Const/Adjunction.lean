module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant diagrams and endpoint evaluation

If an indexing category has a chosen initial object, a morphism from a constant diagram is
determined by its component there.  Dually, a morphism to a constant diagram is determined at a
chosen terminal object.  This file exposes the reconstruction maps, Hom equivalences, and the two
resulting adjunctions without imposing limits or colimits on the target category.
-/

@[expose] public section

open CategoryTheory

universe uJ vJ uC vC

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

namespace IsInitial

variable {j : J} (h : IsInitial j)

/-- Extend a morphism into the value at an initial object to a morphism from a constant diagram. -/
@[stacks 0G5Q "constant-diagram reconstruction from an initial value"]
def constTo {X : C} {F : J ⥤ C} (f : X ⟶ F.obj j) :
    (Functor.const J).obj X ⟶ F :=
  (limitOfDiagramInitial h F).homEquiv f

/-- The reconstructed transformation has the defining component formula. -/
@[simp, stacks 0G5Q "constant-diagram reconstruction component"]
theorem constTo.app {X : C} {F : J ⥤ C} (f : X ⟶ F.obj j) (a : J) :
    (h.constTo f).app a = f ≫ F.map (h.to a) := sorry

/-- Reconstruction at the initial object recovers the given morphism. -/
@[simp, stacks 0G5Q "constant-diagram reconstruction at the initial object"]
theorem constTo.app_self {X : C} {F : J ⥤ C} (f : X ⟶ F.obj j) :
    (h.constTo f).app j = f := sorry

/-- A transformation from a constant diagram is reconstructed from its initial component. -/
@[stacks 0G5Q "constant-diagram reconstruction inverse law"]
theorem constTo.of_app {X : C} {F : J ⥤ C}
    (alpha : (Functor.const J).obj X ⟶ F) :
    h.constTo (alpha.app j) = alpha := sorry

/-- Transformations from a constant diagram are determined at an initial object. -/
@[ext, stacks 0G5Q "constant-diagram morphism extensionality"]
theorem constTo.hom_ext {X : C} {F : J ⥤ C}
    {alpha beta : (Functor.const J).obj X ⟶ F}
    (w : alpha.app j = beta.app j) :
    alpha = beta := sorry

/-- Morphisms from a constant diagram are equivalent to morphisms into the value at an initial
object. -/
@[stacks 0G5Q "constant-diagram initial-value Hom equivalence"]
def constHomEquiv (X : C) (F : J ⥤ C) :
    ((Functor.const J).obj X ⟶ F) ≃ (X ⟶ F.obj j) :=
  (limitOfDiagramInitial h F).homEquiv.symm

/-- The forward constant-diagram Hom equivalence is evaluation at the initial object. -/
@[simp, stacks 0G5Q "constant-diagram Hom equivalence evaluation"]
theorem constHomEquiv.apply (X : C) (F : J ⥤ C)
    (alpha : (Functor.const J).obj X ⟶ F) :
    h.constHomEquiv X F alpha = alpha.app j := sorry

/-- The inverse constant-diagram Hom equivalence is `constTo`. -/
@[simp, stacks 0G5Q "constant-diagram Hom equivalence reconstruction"]
theorem constHomEquiv.symm_apply (X : C) (F : J ⥤ C) (f : X ⟶ F.obj j) :
    (h.constHomEquiv X F).symm f = h.constTo f := sorry

/-- The inverse constant-diagram Hom equivalence is natural in the constant value. -/
@[stacks 0G5Q "constant-diagram Hom equivalence source naturality"]
theorem constHomEquiv.symm_precomp
    {X Y : C} {F : J ⥤ C} (f : X ⟶ Y) (g : Y ⟶ F.obj j) :
    (h.constHomEquiv X F).symm (f ≫ g) =
      (Functor.const J).map f ≫ (h.constHomEquiv Y F).symm g := sorry

/-- The constant-diagram Hom equivalence is natural in the target diagram. -/
@[stacks 0G5Q "constant-diagram Hom equivalence target naturality"]
theorem constHomEquiv.postcomp
    {X : C} {F G : J ⥤ C}
    (alpha : (Functor.const J).obj X ⟶ F) (beta : F ⟶ G) :
    h.constHomEquiv X G (alpha ≫ beta) =
      h.constHomEquiv X F alpha ≫ beta.app j := sorry

/-- The constant-diagram functor is left adjoint to evaluation at an initial object. -/
@[stacks 0G5Q "constant-diagram initial-evaluation adjunction"]
def constAdj :
    Functor.const J ⊣ (evaluation J C).obj j :=
  Adjunction.mkOfHomEquiv {
    homEquiv := h.constHomEquiv
    homEquiv_naturality_left_symm := constHomEquiv.symm_precomp h
    homEquiv_naturality_right := constHomEquiv.postcomp h }

end IsInitial

namespace IsTerminal

variable {j : J} (h : IsTerminal j)

/-- Extend a morphism from the value at a terminal object to a morphism into a constant diagram. -/
@[stacks 0G5Q "constant-target reconstruction from a terminal value"]
def toConst {F : J ⥤ C} {X : C} (f : F.obj j ⟶ X) :
    F ⟶ (Functor.const J).obj X :=
  (colimitOfDiagramTerminal h F).homEquiv f

/-- The transformation to a constant diagram has the defining component formula. -/
@[simp, stacks 0G5Q "constant-target reconstruction component"]
theorem toConst.app {F : J ⥤ C} {X : C} (f : F.obj j ⟶ X) (a : J) :
    (h.toConst f).app a = F.map (h.from a) ≫ f := sorry

/-- Reconstruction at the terminal object recovers the given morphism. -/
@[simp, stacks 0G5Q "constant-target reconstruction at the terminal object"]
theorem toConst.app_self {F : J ⥤ C} {X : C} (f : F.obj j ⟶ X) :
    (h.toConst f).app j = f := sorry

/-- A transformation to a constant diagram is reconstructed from its terminal component. -/
@[stacks 0G5Q "constant-target reconstruction inverse law"]
theorem toConst.of_app {F : J ⥤ C} {X : C}
    (alpha : F ⟶ (Functor.const J).obj X) :
    h.toConst (alpha.app j) = alpha := sorry

/-- Transformations to a constant diagram are determined at a terminal object. -/
@[ext, stacks 0G5Q "constant-target morphism extensionality"]
theorem toConst.hom_ext {F : J ⥤ C} {X : C}
    {alpha beta : F ⟶ (Functor.const J).obj X}
    (w : alpha.app j = beta.app j) :
    alpha = beta := sorry

/-- Morphisms from the value at a terminal object are equivalent to morphisms into a constant
diagram. -/
@[stacks 0G5Q "terminal-evaluation constant-target Hom equivalence"]
def evalHomEquiv (F : J ⥤ C) (X : C) :
    (F.obj j ⟶ X) ≃ (F ⟶ (Functor.const J).obj X) :=
  (colimitOfDiagramTerminal h F).homEquiv

/-- The forward terminal-evaluation Hom equivalence is `toConst`. -/
@[simp, stacks 0G5Q "terminal-evaluation Hom equivalence reconstruction"]
theorem evalHomEquiv.apply (F : J ⥤ C) (X : C) (f : F.obj j ⟶ X) :
    h.evalHomEquiv F X f = h.toConst f := sorry

/-- The inverse terminal-evaluation Hom equivalence is evaluation at the terminal object. -/
@[simp, stacks 0G5Q "terminal-evaluation Hom equivalence evaluation"]
theorem evalHomEquiv.symm_apply
    (F : J ⥤ C) (X : C) (alpha : F ⟶ (Functor.const J).obj X) :
    (h.evalHomEquiv F X).symm alpha = alpha.app j := sorry

/-- The inverse terminal-evaluation Hom equivalence is natural in the source diagram. -/
@[stacks 0G5Q "terminal-evaluation Hom equivalence source naturality"]
theorem evalHomEquiv.symm_precomp
    {F G : J ⥤ C} {X : C} (alpha : F ⟶ G)
    (beta : G ⟶ (Functor.const J).obj X) :
    (h.evalHomEquiv F X).symm (alpha ≫ beta) =
      alpha.app j ≫ (h.evalHomEquiv G X).symm beta := sorry

/-- The terminal-evaluation Hom equivalence is natural in the constant value. -/
@[stacks 0G5Q "terminal-evaluation Hom equivalence target naturality"]
theorem evalHomEquiv.postcomp
    {F : J ⥤ C} {X Y : C} (f : F.obj j ⟶ X) (g : X ⟶ Y) :
    h.evalHomEquiv F Y (f ≫ g) =
      h.evalHomEquiv F X f ≫ (Functor.const J).map g := sorry

/-- Evaluation at a terminal object is left adjoint to the constant-diagram functor. -/
@[stacks 0G5Q "terminal-evaluation constant-diagram adjunction"]
def evalAdj :
    (evaluation J C).obj j ⊣ Functor.const J :=
  Adjunction.mkOfHomEquiv {
    homEquiv := h.evalHomEquiv
    homEquiv_naturality_left_symm := evalHomEquiv.symm_precomp h
    homEquiv_naturality_right := evalHomEquiv.postcomp h }

end IsTerminal

end CategoryTheory.Limits
