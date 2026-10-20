module

public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal

/-!
# Lax monoidal functors, internal Hom, and adjunctions

An adjunction specializes the internal-Hom comparison of a lax monoidal left adjoint by
postcomposing with its counit.
-/

@[expose] public section

open CategoryTheory.MonoidalClosed

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor.LaxMonoidal.InternalHom

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]

/-- The internal-Hom comparison of a lax monoidal left adjoint, followed by the map induced by
the counit of the adjunction. -/
noncomputable def adjunctionComparison {G : D ⥤ C} (adj : F ⊣ G)
    (X : C) [Closed X] [Closed (F.obj X)] (Y : D) :
    F.obj ((ihom X).obj (G.obj Y)) ⟶ (ihom (F.obj X)).obj Y :=
  comparison F X (G.obj Y) ≫ (ihom (F.obj X)).map (adj.counit.app Y)

/-- The adjunction internal-Hom comparison factors as the lax-monoidal comparison followed by
the map induced by the counit. -/
theorem adjunctionComparison_eq {G : D ⥤ C} (adj : F ⊣ G)
    (X : C) [Closed X] [Closed (F.obj X)] (Y : D) :
    adjunctionComparison F adj X Y =
      comparison F X (G.obj Y) ≫ (ihom (F.obj X)).map (adj.counit.app Y) := sorry

end CategoryTheory.Functor.LaxMonoidal.InternalHom
