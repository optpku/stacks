/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Pullback of coherent formal modules

This file records the stagewise behavior, existence, and exactness properties of pullback
functors between categories of coherent formal modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A functor between categories of coherent formal modules is a pullback functor along `f` when
its stage objects, transition maps, and morphisms are obtained from `Scheme.Modules.pullback f`.
-/
structure IsCoherentFormalModulesPullbackFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f)) : Prop where
  /-- Every stage object is the ordinary pullback of the corresponding module sheaf. -/
  obj_eq : ∀ (M : CoherentFormalModules Y J) (n : ℕ),
    (((F.obj M).obj).obj (op n)).obj =
      (Scheme.Modules.pullback f).obj (((M.obj).obj (op n)).obj)
  /-- Every internal transition map is the ordinary pullback of the corresponding transition
  map. -/
  transitionMap_eq : ∀ (M : CoherentFormalModules Y J) {i j : ℕ} (hij : i ≤ j),
    ((((F.obj M).obj).transitionMap hij).hom) =
      eqToHom (obj_eq M j) ≫
        (Scheme.Modules.pullback f).map (((M.obj).transitionMap hij).hom) ≫
        eqToHom (obj_eq M i).symm
  /-- Every stagewise component of a morphism is the ordinary pullback of the corresponding
  component. -/
  map_eq : ∀ {M N : CoherentFormalModules Y J} (g : M ⟶ N) (n : ℕ),
    ((F.map g).hom.app (op n)).hom =
      eqToHom (obj_eq M n) ≫
        (Scheme.Modules.pullback f).map ((g.hom.app (op n)).hom) ≫
        eqToHom (obj_eq N n).symm

namespace IsCoherentFormalModulesPullbackFunctor

/-- The stage object of a coherent-formal-module pullback functor is isomorphic to the ordinary
pullback of the corresponding module sheaf. -/
def objIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} {J : Y.IdealSheafData}
    {F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f)}
    (hF : IsCoherentFormalModulesPullbackFunctor f J F)
    (M : CoherentFormalModules Y J) (n : ℕ) :
    (((F.obj M).obj).obj (op n)).obj ≅
      (Scheme.Modules.pullback f).obj (((M.obj).obj (op n)).obj) :=
  eqToIso (hF.obj_eq M n)

end IsCoherentFormalModulesPullbackFunctor

/-- The stage-object, transition-map, and morphism specifications of a coherent-formal-module
pullback functor. -/
theorem isCoherentFormalModulesPullbackFunctor_spec
    {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f))
    (hF : IsCoherentFormalModulesPullbackFunctor f J F) :
    (∀ (M : CoherentFormalModules Y J) (n : ℕ),
      (((F.obj M).obj).obj (op n)).obj =
        (Scheme.Modules.pullback f).obj (((M.obj).obj (op n)).obj)) ∧
      (∀ (M : CoherentFormalModules Y J) {i j : ℕ} (hij : i ≤ j),
        ((((F.obj M).obj).transitionMap hij).hom) =
          eqToHom (hF.obj_eq M j) ≫
            (Scheme.Modules.pullback f).map (((M.obj).transitionMap hij).hom) ≫
            eqToHom (hF.obj_eq M i).symm) ∧
        ∀ {M N : CoherentFormalModules Y J} (g : M ⟶ N) (n : ℕ),
          ((F.map g).hom.app (op n)).hom =
            eqToHom (hF.obj_eq M n) ≫
              (Scheme.Modules.pullback f).map ((g.hom.app (op n)).hom) ≫
              eqToHom (hF.obj_eq N n).symm := by
  exact ⟨hF.obj_eq, hF.transitionMap_eq, hF.map_eq⟩

/-- For a morphism of Noetherian schemes, stagewise pullback determines a functor between the
corresponding categories of coherent formal modules. -/
theorem coherentFormalModules_pullback_exists
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    ∃ F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f),
      IsCoherentFormalModulesPullbackFunctor f J F := sorry

/-- A coherent-formal-module functor given by stagewise pullback along a morphism of Noetherian
schemes is right exact. -/
theorem coherentFormalModules_pullback_rightExact
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData)
    (F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f))
    (hF : IsCoherentFormalModulesPullbackFunctor f J F) :
    rightExactFunctor (CoherentFormalModules Y J)
      (CoherentFormalModules X (J.comap f)) F := sorry

/-- For a morphism of Noetherian schemes, there exists a right exact stagewise pullback functor
between the corresponding categories of coherent formal modules. -/
theorem coherentFormalModules_pullback_exists_rightExact
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    ∃ F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f),
      IsCoherentFormalModulesPullbackFunctor f J F ∧
        rightExactFunctor (CoherentFormalModules Y J)
          (CoherentFormalModules X (J.comap f)) F := by
  obtain ⟨F, hF⟩ := coherentFormalModules_pullback_exists f J
  exact ⟨F, hF, coherentFormalModules_pullback_rightExact f J F hF⟩

/-- Stagewise pullback of coherent formal modules along a flat morphism of Noetherian schemes is
exact. -/
theorem coherentFormalModules_pullback_exact_of_flat
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    (F : CoherentFormalModules Y J ⥤ CoherentFormalModules X (J.comap f))
    (hF : IsCoherentFormalModulesPullbackFunctor f J F) :
    exactFunctor (CoherentFormalModules Y J)
      (CoherentFormalModules X (J.comap f)) F := by
  refine ⟨?_, coherentFormalModules_pullback_rightExact f J F hF⟩
  sorry

namespace CoherentFormalModules

variable {X Y : Scheme.{u}}

/-- Stage `n` of the stagewise pullback of a coherent formal module along `f`. -/
def pullbackStage [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    {J : Y.IdealSheafData} (G : CoherentFormalModules Y J) (n : ℕ) :
    RingedSpace.Coh X.toRingedSpace :=
  ⟨(Modules.pullback f).obj (((G.obj).obj (op n)).obj),
    @Modules.pullback_isCoherent X Y _ _ f
      (((G.obj).obj (op n)).obj) ((G.obj).obj (op n)).property⟩

/-- The underlying module of `pullbackStage` is ordinary pullback of the corresponding stage. -/
theorem pullbackStage_obj [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    {J : Y.IdealSheafData} (G : CoherentFormalModules Y J) (n : ℕ) :
    (pullbackStage f G n).obj = (Modules.pullback f).obj (((G.obj).obj (op n)).obj) :=
  rfl

/-- The stagewise pullback of a coherent formal module along `f`, as an object of
`CoherentFormalModules X (J.comap f)`. -/
def pullbackObj [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : CoherentFormalModules Y J) :
    CoherentFormalModules X (J.comap f) where
  obj :=
    Functor.ofOpSequence fun n ↦
      (ObjectProperty.homMk
        ((Modules.pullback f).map
          (((G.obj).map (homOfLE (Nat.le_add_right n 1)).op).hom)) :
        pullbackStage f G (n + 1) ⟶ pullbackStage f G n)
  property := sorry

/-- Stage `n` of `pullbackObj` is the ordinary module pullback of stage `n`. -/
theorem pullbackObj_stage_obj [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (G : CoherentFormalModules Y J) (n : ℕ) :
    (((pullbackObj f J G).obj).obj (op n)).obj =
      (Modules.pullback f).obj (((G.obj).obj (op n)).obj) :=
  rfl


/-- A stagewise pullback functor along a flat morphism of Noetherian schemes is an equivalence
when the canonical map from the inverse-image closed subscheme is an isomorphism. -/
theorem pullback_isEquivalence
    {X X' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    (f : X' ⟶ X) [Flat f] (I : X.IdealSheafData)
    [IsIso (IdealSheafData.subschemeMap (I.comap f) I f (I.le_map_comap f))]
    (reindex : CoherentFormalModules X I ⥤ CoherentFormalModules X' (I.comap f))
    (hF : IsCoherentFormalModulesPullbackFunctor f I reindex) :
    Functor.IsEquivalence reindex := sorry

end CoherentFormalModules

end AlgebraicGeometry.Scheme
