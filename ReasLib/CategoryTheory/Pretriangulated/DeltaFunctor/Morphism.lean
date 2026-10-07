module

public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Morphisms of Delta Functors

This file equips pretriangulated delta functors with the morphisms that
preserve their connecting maps. The resulting category and faithful
forgetful functor provide the neutral API used by transport and composition.
-/

open CategoryTheory.Pretriangulated

universe vA uA vD uD

namespace CategoryTheory.DeltaFunctor

variable {A : Type uA} {D : Type uD} [Category.{vA} A] [Abelian A]
  [Category.{vD} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The triangle map induced by an identity map of a short exact sequence is
the identity triangle morphism. -/
@[simp, stacks 0150 "identity map of delta-functor triangles"]
theorem triangleMap_id (F : DeltaFunctor A D) {S : ShortComplex A}
    (hS : S.ShortExact) :
    F.triangleMap hS hS (𝟙 S) = 𝟙 (F.triangle hS) := sorry

/-- Triangle maps induced by maps of short exact sequences preserve
composition. -/
@[simp, stacks 0150 "composition of maps of delta-functor triangles"]
theorem triangleMap_comp (F : DeltaFunctor A D) {S T U : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (hU : U.ShortExact)
    (f : S ⟶ T) (g : T ⟶ U) :
    F.triangleMap hS hU (f ≫ g) =
      F.triangleMap hS hT f ≫ F.triangleMap hT hU g := sorry

/-- A morphism of pretriangulated delta functors is a natural transformation
of the underlying functors that commutes with every connecting morphism. -/
@[ext, stacks 0150 "morphism of delta functors"]
structure Hom (F G : DeltaFunctor A D) where
  /-- The natural transformation between the underlying functors. -/
  app : F.toFunctor ⟶ G.toFunctor
  /-- Compatibility with the connecting morphism of every short exact
  sequence. -/
  comm ⦃S : ShortComplex A⦄ (hS : S.ShortExact) :
    CommSq (app.app S.X₃) (F.δ hS) (G.δ hS)
      ((app.app S.X₁)⟦(1 : ℤ)⟧')

namespace Hom

/-- The compatibility square of a delta-functor morphism, written as an
equality with the connecting maps first. -/
@[reassoc, stacks 0150 "delta-functor morphism compatibility"]
theorem comm_eq {F G : DeltaFunctor A D} (f : Hom F G)
    {S : ShortComplex A} (hS : S.ShortExact) :
    F.δ hS ≫ (f.app.app S.X₁)⟦(1 : ℤ)⟧' =
      f.app.app S.X₃ ≫ G.δ hS := sorry

/-- The identity morphism of a pretriangulated delta functor. -/
def id (F : DeltaFunctor A D) : Hom F F where
  app := 𝟙 F.toFunctor
  comm := sorry

/-- Composition of morphisms of pretriangulated delta functors. -/
def comp {F G H : DeltaFunctor A D} (f : Hom F G) (g : Hom G H) : Hom F H where
  app := f.app ≫ g.app
  comm := sorry

end Hom

/-- Pretriangulated delta functors form a category under transformations that
preserve connecting morphisms. -/
instance : Category (DeltaFunctor A D) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The underlying natural transformation of the identity delta-functor
morphism is the identity. -/
@[simp]
theorem id_app (F : DeltaFunctor A D) :
    (𝟙 F : F ⟶ F).app = 𝟙 F.toFunctor := sorry

/-- The underlying natural transformation of a composite delta-functor
morphism is the composite transformation. -/
@[simp]
theorem comp_app {F G H : DeltaFunctor A D} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).app = f.app ≫ g.app := sorry

/-- Forget the connecting maps of a pretriangulated delta functor. -/
@[stacks 0150 "forgetful functor from delta functors"]
def forget : DeltaFunctor A D ⥤ A ⥤ D where
  obj F := F.toFunctor
  map f := f.app
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor from pretriangulated delta functors is faithful. -/
instance forget_faithful : (forget : DeltaFunctor A D ⥤ A ⥤ D).Faithful := sorry

/-- Forgetting a delta functor returns its underlying functor. -/
@[simp]
theorem forget_obj (F : DeltaFunctor A D) :
    (forget : DeltaFunctor A D ⥤ A ⥤ D).obj F = F.toFunctor := sorry

/-- Forgetting a delta-functor morphism returns its underlying natural
transformation. -/
@[simp]
theorem forget_map {F G : DeltaFunctor A D} (f : F ⟶ G) :
    (forget : DeltaFunctor A D ⥤ A ⥤ D).map f = f.app := sorry

end CategoryTheory.DeltaFunctor
