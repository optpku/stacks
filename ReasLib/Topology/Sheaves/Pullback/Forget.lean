module

public import Mathlib.Topology.Sheaves.Functors

/-!
# Forgetting sheaf pullback along an open embedding

This file compares the canonical pullback of sheaves along an open embedding with presheaf
pullback after forgetting the sheaf condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe w u

namespace Topology.IsOpenEmbedding

variable {Y X : TopCat.{w}} {f : X ⟶ Y}
variable {C : Type u} [Category.{w} C] [HasColimits C] [HasLimits C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{w} C FC]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

/-- Along an open embedding, forgetting the canonical sheaf pullback agrees with presheaf
pullback. -/
noncomputable def pullbackForgetIso (hf : IsOpenEmbedding f) :
    TopCat.Sheaf.forget C Y ⋙ TopCat.Presheaf.pullback C f ≅
      TopCat.Sheaf.pullback C f ⋙ TopCat.Sheaf.forget C X :=
  Functor.isoWhiskerLeft (TopCat.Sheaf.forget C Y) hf.isOpenMap.pullbackIso ≪≫
    (Functor.isoWhiskerRight (hf.sheafPullbackIso C)
      (TopCat.Sheaf.forget C X)).symm

end Topology.IsOpenEmbedding
