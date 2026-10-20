/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Exact.Abelian
public import ReasLib.CategoryTheory.Exact.SheafYoneda
public import ReasLib.CategoryTheory.Exact.Site.FiniteRefinement
public import ReasLib.CategoryTheory.Functor.Exactness

@[expose] public section

/-!
# Sheaf-Valued Yoneda for Abelian Categories

The additive Yoneda embedding of an abelian category lands in sheaves for the singleton-
epimorphism topology.  This specialization of the exact-structure Yoneda embedding is fully
faithful and exact, and its site has enough points.
-/

open CategoryTheory Limits

universe u v

noncomputable section

namespace CategoryTheory.Abelian

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Additive representables are sheaves for the epimorphism topology. -/
theorem preadditiveYoneda_isSheaf (X : A) :
    Presheaf.IsSheaf (epiTopology A) (preadditiveYoneda.obj X) := sorry

/-- The sheaf-valued additive Yoneda embedding for the epimorphism topology of an abelian
category. -/
@[stacks 05PN "sheaf-valued Yoneda embedding"]
abbrev sheafYoneda : A ⥤ Sheaf (epiTopology A) AddCommGrpCat.{v} :=
  (ExactStructure.ofAbelian A).sheafYoneda

/-- The sheaf-valued Yoneda embedding maps short exact sequences to short exact sequences. -/
theorem sheafYoneda_maps_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map (sheafYoneda A)).ShortExact := sorry

/-- The sheaf-valued Yoneda embedding reflects short exact sequences. -/
theorem sheafYoneda_reflects_shortExact {S : ShortComplex A}
    (hS : (S.map (sheafYoneda A)).ShortExact) :
    S.ShortExact := sorry

/-- A short complex is short exact exactly when its image under the sheaf-valued Yoneda embedding
is short exact. -/
@[stacks 05PN "short exactness detected by sheaf-valued Yoneda"]
theorem sheafYoneda_shortExact_iff {S : ShortComplex A} :
    (S.map (sheafYoneda A)).ShortExact ↔ S.ShortExact := sorry

/-- The sheaf-valued Yoneda embedding preserves finite limits. -/
instance sheafYoneda_preservesFiniteLimits : PreservesFiniteLimits (sheafYoneda A) := sorry

/-- The sheaf-valued Yoneda embedding preserves finite colimits. -/
instance sheafYoneda_preservesFiniteColimits : PreservesFiniteColimits (sheafYoneda A) := sorry

/-- Lemma 19.9.2 (05PN): the fully faithful exact sheaf-valued Yoneda embedding for an abelian
category. -/
@[stacks 05PN "exact sheaf-valued Yoneda embedding"]
def sheafYonedaExact :
    A ⥤ₑ Sheaf (epiTopology A) AddCommGrpCat.{v} :=
  ExactFunctor.of (sheafYoneda A)

/-- Lemma 19.9.2 (05PN): the singleton-epimorphism topology on an abelian category has enough
points. -/
@[stacks 05PN "enough points"]
instance epiTopology_hasEnoughPoints :
    GrothendieckTopology.HasEnoughPoints.{max (u + 1) (v + 1)} (epiTopology A) := sorry

#synth Functor.Full (sheafYoneda A)
#synth Functor.Faithful (sheafYoneda A)

end CategoryTheory.Abelian
