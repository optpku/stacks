module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of constant abelian sheaves

The constant-sheaf functor on abelian groups is exact.  Its underlying
presheaf, and hence evaluation at any object of the site, remains exact on
constant short exact sequences.  These are functorial owner statements rather
than presentation-specific proofs.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]

namespace ConstantSheaf

/-- The constant abelian-sheaf functor canonically preserves zero morphisms. -/
noncomputable instance abelian_preservesZeroMorphisms :
    (constantSheaf J AddCommGrpCat.{w}).PreservesZeroMorphisms := sorry

/-- Lemma 18.42.1 (093J), functor form: the constant abelian-sheaf functor
is exact. -/
@[stacks 093J "sheaf exactness"]
theorem abelian_exact :
    exactFunctor AddCommGrpCat.{w} (Sheaf J AddCommGrpCat.{w})
      (constantSheaf J AddCommGrpCat.{w}) := sorry

end ConstantSheaf

/-- A short exact sequence of abelian groups remains short exact after taking
constant sheaves. -/
theorem ShortComplex.ShortExact.map_constantAbelianSheaf
    {S : ShortComplex AddCommGrpCat.{w}} (hS : S.ShortExact) :
    (S.map (constantSheaf J AddCommGrpCat.{w})).ShortExact := sorry

/-- Lemma 18.42.1 (093J), presheaf form: the underlying presheaves of a
constant short exact sequence form a short exact sequence. -/
@[stacks 093J "presheaf exactness"]
theorem ShortComplex.ShortExact.map_constantAbelianPresheaf
    {S : ShortComplex AddCommGrpCat.{w}} (hS : S.ShortExact) :
    ((S.map (constantSheaf J AddCommGrpCat.{w})).map
      (sheafToPresheaf J AddCommGrpCat.{w})).ShortExact := sorry

/-- Evaluating a constant short exact sequence at an object of the site gives
a short exact sequence of abelian groups. -/
theorem ShortComplex.ShortExact.map_constantAbelianSheaf_app
    {S : ShortComplex AddCommGrpCat.{w}} (hS : S.ShortExact) (U : C) :
    (((S.map (constantSheaf J AddCommGrpCat.{w})).map
      (sheafToPresheaf J AddCommGrpCat.{w})).map
        ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op U))).ShortExact := sorry

end CategoryTheory
