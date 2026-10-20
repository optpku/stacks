/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stagewise injective enlargements of compatible sheaf families

This leaf records the stagewise injective-enlargement property for a compatible family on a
cofiltered diagram of sites.  The predicates are coefficient-independent; the existence theorem
uses the canonical Grothendieck structure on abelian sheaves.
-/

@[expose] public section

open CategoryTheory

universe uI uC vC w

namespace CategoryTheory.CofilteredSiteDiagram.StageFamily

/-- A compatible family is stagewise injective when each of its sheaves is injective. -/
@[stacks 0EXZ "stagewise injective family"]
class IsStagewiseInjective
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F : StageFamily S A) : Prop where
  /-- Every stage object of a stagewise injective family is injective. -/
  injective_obj (i : S.I) : Injective (F.obj i)

attribute [instance] IsStagewiseInjective.injective_obj

/-- A morphism of compatible families is stagewise monomorphic when every component is mono. -/
@[stacks 0EXZ "stagewise monomorphic family map"]
class Hom.IsStagewiseMono
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    {F G : StageFamily S A} (f : F ⟶ G) : Prop where
  /-- Every component of a stagewise monomorphic family map is mono. -/
  mono_app (i : S.I) : Mono (f.app i)

attribute [instance] Hom.IsStagewiseMono.mono_app

/-- Lemma 21.16.5 (0EXZ): every compatible family of abelian sheaves admits a morphism to a
stagewise injective family whose component maps are monomorphisms. -/
@[stacks 0EXZ "stagewise injective enlargement"]
theorem exists_mono_to_injective
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (F : StageFamily S AddCommGrpCat.{max uC vC}) :
    ∃ (G : StageFamily S AddCommGrpCat.{max uC vC}) (f : F ⟶ G),
      IsStagewiseInjective G ∧ Hom.IsStagewiseMono f := sorry

end CategoryTheory.CofilteredSiteDiagram.StageFamily
