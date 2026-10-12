/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity and composition laws for based inertia

The forgetful-map and identity-section naturality equalities for relative and
absolute inertia, together with strict identity and composition laws for the
underlying `1`-cell action.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂' u₃ v₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section Comparison

variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₁' : BasedCategory.{v₁', u₁'} C}
    {S₂ : BasedCategory.{v₂, u₂} C} {S₂' : BasedCategory.{v₂', u₂'} C}

/-- Mapping relative inertia commutes with forgetting to the source side of the square. -/
@[simp, stacks 04Z4 "relative-inertia map forgetful compatibility"]
theorem RelativeInertia.map.comp_forget
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) :
    RelativeInertia.map G G' comm ⋙ RelativeInertia.forget F₂ =
      RelativeInertia.forget F₁ ⋙ G := sorry
/- Proof strategy: apply `BasedFunctor.ext`; both underlying functors forget the automorphism
and then apply `G`. -/

/-- Mapping relative inertia carries the neutral section to the neutral section. -/
@[simp, stacks 04Z4 "relative-inertia map neutral-section compatibility"]
theorem RelativeInertia.identitySection.comp_map
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) :
    RelativeInertia.identitySection F₁ ⋙ RelativeInertia.map G G' comm =
      G ⋙ RelativeInertia.identitySection F₂ := sorry
/- Proof strategy: apply `BasedFunctor.ext`; both functors send an object through `G` and equip
it with the identity automorphism. -/

/-- Mapping absolute inertia commutes with its forgetful map. -/
@[simp, stacks 04Z4 "absolute-inertia map forgetful compatibility"]
theorem Inertia.map.comp_forget (G : S₁ ⥤ᵇ S₂) :
    Inertia.map G ⋙ Inertia.forget S₂ = Inertia.forget S₁ ⋙ G := sorry
/- Proof strategy: specialize `RelativeInertia.map.comp_forget` to the structure functors. -/

/-- Mapping absolute inertia carries the neutral section to the neutral section. -/
@[simp, stacks 04Z4 "absolute-inertia map neutral-section compatibility"]
theorem Inertia.identitySection.comp_map (G : S₁ ⥤ᵇ S₂) :
    Inertia.identitySection S₁ ⋙ Inertia.map G =
      G ⋙ Inertia.identitySection S₂ := sorry
/- Proof strategy: specialize `RelativeInertia.identitySection.comp_map` to the structure
functors. -/

/-- Absolute inertia maps identity based functors to identity based functors. -/
@[simp, stacks 04Z4 "absolute-inertia map identity"]
theorem Inertia.map.id (S : BasedCategory.{v₁, u₁} C) :
    Inertia.map (𝟭 S) = 𝟭 (inertia S) := sorry
/- Proof strategy: apply `BasedFunctor.ext` and the identity law for neutral inertia maps. -/

/-- Absolute inertia maps composites to composites. -/
@[simp, stacks 04Z4 "absolute-inertia map composition"]
theorem Inertia.map.comp
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) :
    Inertia.map (G ⋙ H) = Inertia.map G ⋙ Inertia.map H := sorry
/- Proof strategy: apply `BasedFunctor.ext`; use functoriality of `mapIso` on automorphisms and
proof irrelevance for the base-square witnesses. -/

end Comparison

end BasedCategory
end CategoryTheory
