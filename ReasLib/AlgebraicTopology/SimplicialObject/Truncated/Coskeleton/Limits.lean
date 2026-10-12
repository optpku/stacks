/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.CategoryTheory.Functor.RightKanExtension.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018C

# Objectwise coskeletons and limits

This file specializes the objectwise right-Kan-extension limit API to coskeletons of truncated
simplicial objects. The basic universal and map API is owned by `Truncated.KanExtension`; this
leaf only assumes the chosen coskeletons needed by each limit statement.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₀ v₁ u₀ u₁

namespace CategoryTheory.SimplicialObject.Truncated.coskeleton

variable {J : Type u₀} [Category.{v₀} J]
variable {C : Type u₁} [Category.{v₁} C] {n : ℕ}

/-- The diagram obtained by taking the chosen coskeleton of each object and the induced map of
each arrow. -/
@[stacks 018C "diagram of chosen objectwise coskeletons"]
noncomputable def diagram (K : J ⥤ SimplicialObject.Truncated C n)
    [∀ j, (K.obj j).HasCoskeleton] : J ⥤ SimplicialObject C :=
  Functor.RightKanExtension.diagram
    (SimplexCategory.Truncated.inclusion n).op K

namespace limit

variable (K : J ⥤ SimplicialObject.Truncated C n) [HasLimit K]
variable [∀ j, (K.obj j).HasCoskeleton]
variable [(Limits.limit K).HasCoskeleton]

/-- The canonical cone from the coskeleton of a source limit to the diagram of chosen
objectwise coskeletons. -/
@[stacks 018C "objectwise coskeleton limit cone",
  stacks 018D "objectwise coskeleton pullback cone"]
noncomputable def cone : Cone (diagram K) :=
  Functor.RightKanExtension.limit.cone
    (SimplexCategory.Truncated.inclusion n).op K

/-- The coskeleton of a source limit is a limit of the chosen objectwise coskeletons. -/
@[stacks 018C "objectwise coskeletons preserve limits",
  stacks 018D "objectwise coskeletons preserve pullbacks"]
noncomputable def isLimit : IsLimit (cone K) :=
  Functor.RightKanExtension.limit.isLimit
    (SimplexCategory.Truncated.inclusion n).op K

/-- The canonical comparison between the coskeleton of a source limit and the chosen target
limit of objectwise coskeletons. -/
@[stacks 018C "objectwise coskeleton limit comparison",
  stacks 018D "objectwise coskeleton pullback comparison"]
noncomputable def iso [HasLimit (diagram K)] :
    (Limits.limit K).coskeleton ≅ Limits.limit (diagram K) :=
  Functor.RightKanExtension.limit.iso
    (SimplexCategory.Truncated.inclusion n).op K

/-- The forward coskeleton limit comparison computes on every limit projection. -/
@[reassoc (attr := simp), stacks 018C "objectwise coskeleton limit comparison on projections",
  stacks 018D "objectwise coskeleton pullback comparison on projections"]
theorem iso_hom_π [HasLimit (diagram K)] (j : J) :
    (iso K).hom ≫ Limits.limit.π (diagram K) j =
      map (Limits.limit.π K j) := sorry

/-- The inverse coskeleton limit comparison recovers every chosen target-limit projection. -/
@[reassoc (attr := simp),
  stacks 018C "inverse objectwise coskeleton limit comparison on projections",
  stacks 018D "inverse objectwise coskeleton pullback comparison on projections"]
theorem iso_inv_π [HasLimit (diagram K)] (j : J) :
    (iso K).inv ≫ map (Limits.limit.π K j) =
      Limits.limit.π (diagram K) j := sorry

end limit

namespace prod

variable (U V : SimplicialObject.Truncated C n) [HasBinaryProduct U V]
variable [U.HasCoskeleton] [V.HasCoskeleton] [(U ⨯ V).HasCoskeleton]

/-- The binary fan exhibiting the coskeleton of `U ⨯ V` as an objectwise product. -/
@[stacks 018C "objectwise coskeleton product cone"]
noncomputable def cone : BinaryFan U.coskeleton V.coskeleton :=
  Functor.RightKanExtension.prod.cone
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The coskeleton of `U ⨯ V` is a product of the chosen coskeletons of `U` and `V`. -/
@[stacks 018C "objectwise coskeleton product limit"]
noncomputable def isLimit : IsLimit (cone U V) :=
  Functor.RightKanExtension.prod.isLimit
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The canonical product comparison for chosen objectwise coskeletons. -/
@[stacks 018C "objectwise coskeleton product comparison"]
noncomputable def iso [HasBinaryProduct U.coskeleton V.coskeleton] :
    (U ⨯ V).coskeleton ≅ U.coskeleton ⨯ V.coskeleton :=
  Functor.RightKanExtension.prod.iso
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The product comparison followed by the first projection is induced by the source first
projection. -/
@[reassoc (attr := simp), stacks 018C "objectwise coskeleton product comparison first projection"]
theorem iso_hom_fst [HasBinaryProduct U.coskeleton V.coskeleton] :
    (iso U V).hom ≫ Limits.prod.fst =
      map (Limits.prod.fst : U ⨯ V ⟶ U) := sorry

/-- The product comparison followed by the second projection is induced by the source second
projection. -/
@[reassoc (attr := simp), stacks 018C "objectwise coskeleton product comparison second projection"]
theorem iso_hom_snd [HasBinaryProduct U.coskeleton V.coskeleton] :
    (iso U V).hom ≫ Limits.prod.snd =
      map (Limits.prod.snd : U ⨯ V ⟶ V) := sorry

/-- The inverse product comparison followed by the induced first projection recovers the chosen
target first projection. -/
@[reassoc (attr := simp), stacks 018C "inverse objectwise coskeleton product first projection"]
theorem iso_inv_fst [HasBinaryProduct U.coskeleton V.coskeleton] :
    (iso U V).inv ≫ map (Limits.prod.fst : U ⨯ V ⟶ U) =
      Limits.prod.fst := sorry

/-- The inverse product comparison followed by the induced second projection recovers the chosen
target second projection. -/
@[reassoc (attr := simp), stacks 018C "inverse objectwise coskeleton product second projection"]
theorem iso_inv_snd [HasBinaryProduct U.coskeleton V.coskeleton] :
    (iso U V).inv ≫ map (Limits.prod.snd : U ⨯ V ⟶ V) =
      Limits.prod.snd := sorry

end prod

namespace pullback

variable {U V W : SimplicialObject.Truncated C n} (f : U ⟶ V) (g : W ⟶ V)
variable [HasPullback f g]
variable [U.HasCoskeleton] [V.HasCoskeleton] [W.HasCoskeleton]
variable [(Limits.pullback f g).HasCoskeleton]

/-- The maps induced by the source pullback projections satisfy the target pullback
condition. -/
@[stacks 018D "objectwise coskeleton pullback condition"]
theorem condition :
    map (Limits.pullback.fst f g) ≫ map f =
      map (Limits.pullback.snd f g) ≫ map g := sorry

/-- The pullback cone whose point is the coskeleton of the source pullback. -/
@[stacks 018D "objectwise coskeleton pullback cone"]
noncomputable def cone : PullbackCone (map f) (map g) :=
  Functor.RightKanExtension.pullback.cone
    (SimplexCategory.Truncated.inclusion n).op f g

/-- The coskeleton of the source pullback is a pullback of the three chosen objectwise
coskeletons. -/
@[stacks 018D "objectwise coskeleton pullback limit"]
noncomputable def isLimit : IsLimit (cone f g) :=
  Functor.RightKanExtension.pullback.isLimit
    (SimplexCategory.Truncated.inclusion n).op f g

/-- The canonical pullback comparison for chosen objectwise coskeletons. -/
@[stacks 018D "objectwise coskeleton pullback comparison"]
noncomputable def iso [HasPullback (map f) (map g)] :
    (Limits.pullback f g).coskeleton ≅ Limits.pullback (map f) (map g) :=
  Functor.RightKanExtension.pullback.iso
    (SimplexCategory.Truncated.inclusion n).op f g

/-- The pullback comparison followed by the first projection is induced by the source first
projection. -/
@[reassoc (attr := simp), stacks 018D "objectwise coskeleton pullback comparison first projection"]
theorem iso_hom_fst [HasPullback (map f) (map g)] :
    (iso f g).hom ≫ Limits.pullback.fst (map f) (map g) =
      map (Limits.pullback.fst f g) := sorry

/-- The pullback comparison followed by the second projection is induced by the source second
projection. -/
@[reassoc (attr := simp), stacks 018D "objectwise coskeleton pullback comparison second projection"]
theorem iso_hom_snd [HasPullback (map f) (map g)] :
    (iso f g).hom ≫ Limits.pullback.snd (map f) (map g) =
      map (Limits.pullback.snd f g) := sorry

/-- The inverse pullback comparison followed by the induced first projection recovers the chosen
target first projection. -/
@[reassoc (attr := simp), stacks 018D "inverse objectwise coskeleton pullback first projection"]
theorem iso_inv_fst [HasPullback (map f) (map g)] :
    (iso f g).inv ≫ map (Limits.pullback.fst f g) =
      Limits.pullback.fst (map f) (map g) := sorry

/-- The inverse pullback comparison followed by the induced second projection recovers the chosen
target second projection. -/
@[reassoc (attr := simp), stacks 018D "inverse objectwise coskeleton pullback second projection"]
theorem iso_inv_snd [HasPullback (map f) (map g)] :
    (iso f g).inv ≫ map (Limits.pullback.snd f g) =
      Limits.pullback.snd (map f) (map g) := sorry

end pullback

end CategoryTheory.SimplicialObject.Truncated.coskeleton
