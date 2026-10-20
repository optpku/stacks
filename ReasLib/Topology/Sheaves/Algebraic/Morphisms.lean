module

public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
public import ReasLib.Topology.Sheaves.Stalks.Filtered

/-!
# Morphisms of algebraic-structure-valued sheaves

The lifting criteria here turn structure-preserving maps of underlying sheaves into morphisms in
the original coefficient category.

## Main declarations

- `TopCat.Sheaf.Algebraic.existsUnique_hom_of_stalkwise`: an underlying morphism whose stalk maps
  are all induced by `C`-morphisms lifts uniquely to `C`
- `TopCat.Sheaf.Algebraic.existsUnique_pushforwardHom_of_sectionwise`: the analogous criterion
  for pushforward targets, using section-level lifts
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open TopCat.Presheaf

noncomputable section

universe w v u

namespace TopCat.Sheaf.Algebraic

/-- An underlying morphism of set-valued sheaves whose stalk maps are each induced by a
morphism in `C` lifts uniquely to a morphism of `C`-valued sheaves. -/
@[stacks 007W "stalkwise structure-preserving morphism lifts uniquely"]
theorem existsUnique_hom_of_stalkwise
    {C : Type u} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]
    {X : TopCat.{w}} {ℱ 𝒢 : X.Sheaf C}
    (φ : (sheafCompose (Opens.grothendieckTopology X) F).obj ℱ ⟶
      (sheafCompose (Opens.grothendieckTopology X) F).obj 𝒢)
    (hφ : ∀ x : X, ∃ ψx : filteredStalk x ℱ.presheaf ⟶ filteredStalk x 𝒢.presheaf,
      (stalkCompIso x F ℱ.presheaf).hom ≫
          (TopCat.Presheaf.stalkFunctor (Type w) x).map (CategoryTheory.Sheaf.homEquiv φ) ≫
          (stalkCompIso x F 𝒢.presheaf).inv =
        F.map ψx) :
    ∃! Φ : ℱ ⟶ 𝒢,
      (sheafCompose (Opens.grothendieckTopology X) F).map Φ = φ := sorry

/-- A morphism between underlying set-valued sheaves into a pushforward lifts uniquely to the
original coefficient category when every section map is induced by a morphism there. -/
theorem existsUnique_pushforwardHom_of_sectionwise
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [F.Faithful]
    {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ : X.Sheaf C} {𝒢 : Y.Sheaf C}
    [(Opens.grothendieckTopology Y).HasSheafCompose F]
    (φ : (sheafCompose (Opens.grothendieckTopology Y) F).obj 𝒢 ⟶
      (sheafCompose (Opens.grothendieckTopology Y) F).obj
        ((TopCat.Sheaf.pushforward C f).obj ℱ))
    (hφ : ∀ V : Opens Y, ∃ ψV : 𝒢.presheaf.obj (op V) ⟶
        ((TopCat.Sheaf.pushforward C f).obj ℱ).presheaf.obj (op V),
      F.map ψV = (CategoryTheory.Sheaf.homEquiv φ).app (op V)) :
    ∃! Φ : 𝒢 ⟶ (TopCat.Sheaf.pushforward C f).obj ℱ,
      (sheafCompose (Opens.grothendieckTopology Y) F).map Φ = φ := sorry

end TopCat.Sheaf.Algebraic

end

end
