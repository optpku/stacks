/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Morphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Transporting Delta Functors

This leaf transports a delta-functor structure across a natural isomorphism
of its underlying functor.  It keeps model-specific constructions out of
downstream APIs: a convenient functor model may carry the original structure,
while consumers use any canonically isomorphic functor.
-/

open CategoryTheory.Pretriangulated

universe vA uA vD uD

namespace CategoryTheory.DeltaFunctor

variable {A : Type uA} {D : Type uD} [Category.{vA} A] [Abelian A]
  [Category.{vD} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Transport a delta-functor structure across an isomorphism of its underlying functor. -/
@[stacks 0150 "delta functor transport"]
def transport (F : DeltaFunctor A D) {G : A ⥤ D} (e : F.toFunctor ≅ G) :
    DeltaFunctor A D where
  toFunctor := G
  additive := @Functor.additive_of_iso _ _ _ _ _ _ F.toFunctor F.additive G e
  δ := fun {S} hS ↦ e.inv.app S.X₃ ≫ F.δ hS ≫ (e.hom.app S.X₁)⟦(1 : ℤ)⟧'
  map_distinguished := sorry
  δ_naturality := sorry

/-- The underlying functor of a transported delta functor is the target functor. -/
@[simp, stacks 0150 "delta functor transport computation"]
theorem transport_toFunctor (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) :
    (F.transport e).toFunctor = G := sorry

/-- Transport does not change the object function beyond the supplied natural isomorphism. -/
@[simp, stacks 0150 "delta functor transport computation"]
theorem transport_obj (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) (X : A) :
    (F.transport e).obj X = G.obj X := sorry

/-- Transport does not change the morphism function beyond the supplied natural isomorphism. -/
@[simp, stacks 0150 "delta functor transport computation"]
theorem transport_map (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) {X Y : A} (f : X ⟶ Y) :
    (F.transport e).map f = G.map f := sorry

/-- The connecting morphism of a transported delta functor is obtained by conjugating the
original connecting morphism by the supplied natural isomorphism. -/
@[simp, stacks 0150 "delta functor transport computation"]
theorem transport_δ (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) {S : ShortComplex A} (hS : S.ShortExact) :
    (F.transport e).δ hS =
      e.inv.app S.X₃ ≫ F.δ hS ≫ (e.hom.app S.X₁)⟦(1 : ℤ)⟧' := sorry

/-- Transport is canonically isomorphic to the original delta functor by the
natural isomorphism used to transport its structure. -/
@[stacks 0150 "delta functor transport isomorphism"]
def transportIso (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) : F ≅ F.transport e where
  hom :=
    { app := e.hom
      comm := sorry }
  inv :=
    { app := e.inv
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward underlying transformation of `transportIso` is the supplied
natural isomorphism. -/
@[simp]
theorem transportIso_hom_app (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) :
    (F.transportIso e).hom.app = e.hom := sorry

/-- The inverse underlying transformation of `transportIso` is the supplied
inverse natural transformation. -/
@[simp]
theorem transportIso_inv_app (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) :
    (F.transportIso e).inv.app = e.inv := sorry

/-- Forgetting the transport isomorphism recovers the natural isomorphism
used to transport the delta-functor structure. -/
@[simp]
theorem forget_mapIso_transportIso (F : DeltaFunctor A D) {G : A ⥤ D}
    (e : F.toFunctor ≅ G) :
    (forget : DeltaFunctor A D ⥤ A ⥤ D).mapIso (F.transportIso e) = e := sorry

end CategoryTheory.DeltaFunctor
