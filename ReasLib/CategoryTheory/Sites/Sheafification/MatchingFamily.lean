/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Refinement of matching families

This leaf supplies the refinement congruence API for mathlib's concrete
matching families `GrothendieckTopology.Meq`. It is independent of a chosen
sheafification coefficient category beyond concreteness.
-/

@[expose] public section

open CategoryTheory Opposite

universe t w' w v u

namespace CategoryTheory.GrothendieckTopology.Meq

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable {FD : D → D → Type*} {CD : D → Type t}
variable [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{t} D FD]

/-- Refining a matching family depends only on the source and target covers,
not on the selected refinement morphism. -/
theorem refine_eq
    {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X}
    (x : Meq P T) (e e' : S ⟶ T) :
    x.refine e = x.refine e' := sorry

/-- After pulling back a matching family, refinement into the pullback cover
is independent of the selected refinement morphism. -/
theorem pullback_refine_eq
    {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover Y} {T : J.Cover X}
    (x : Meq P T) (f : Y ⟶ X) (e e' : S ⟶ (J.pullback f).obj T) :
    (x.pullback f).refine e = (x.pullback f).refine e' := sorry

/-- Matching families for two covers which refine each other are identified by
transport along the equality of covers induced by antisymmetry. -/
@[stacks 00W8]
def mutualRefinementEquiv
    {X : C} {P : Cᵒᵖ ⥤ D} {𝒰 𝒱 : J.Cover X}
    (hUV : 𝒰 ⟶ 𝒱) (hVU : 𝒱 ⟶ 𝒰) :
    Meq P 𝒰 ≃ Meq P 𝒱 :=
  Equiv.cast (congrArg (Meq P) (le_antisymm (leOfHom hUV) (leOfHom hVU)))

/-- `mutualRefinementEquiv` is the canonical `Equiv.cast` along the equality
of covers supplied by the two refinement morphisms. -/
theorem mutualRefinementEquiv_def
    {X : C} {P : Cᵒᵖ ⥤ D} {𝒰 𝒱 : J.Cover X}
    (hUV : 𝒰 ⟶ 𝒱) (hVU : 𝒱 ⟶ 𝒰) :
    mutualRefinementEquiv hUV hVU =
      Equiv.cast (congrArg (Meq P) (le_antisymm (leOfHom hUV) (leOfHom hVU))) := sorry

end CategoryTheory.GrothendieckTopology.Meq
