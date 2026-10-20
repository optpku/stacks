/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of mapped homological complexes

Mathlib's composition isomorphism takes additive structures through typeclass search.  This leaf
also exposes an explicit-witness bridge for applications where a composed functor is definitionally
equal to a standard composite but elaboration cannot recover the three additive instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe vC uC vD uD vE uE uI

namespace CategoryTheory.Functor.MapHomologicalComplex

variable {C : Type uC} {D : Type uD} {E : Type uE}
variable [Category.{vC} C] [Preadditive C]
variable [Category.{vD} D] [Preadditive D]
variable [Category.{vE} E] [Preadditive E]

/-- A bridge supplying explicit additive structures to the standard mapped-complex composition
isomorphism. -/
@[stacks 014W "mapped-complex composition with explicit additive structures"]
noncomputable def compIsoOf
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (hF : F.Additive) (hG : G.Additive) (hH : H.Additive)
    (e : F ⋙ G ≅ H) {I : Type uI} (c : ComplexShape I) :
    F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅ H.mapHomologicalComplex c :=
  letI := hF
  letI := hG
  letI := hH
  Functor.mapHomologicalComplexCompIso e c

end CategoryTheory.Functor.MapHomologicalComplex

end
