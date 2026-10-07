module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap76.Lemma_76_42_1_Category

/-!
# Pullback of coherent formal modules on algebraic spaces

This file records the canonical stagewise pullback functor on coherent formal
modules, étale-local exactness, and exactness along flat morphisms.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Module pullback along a morphism of locally Noetherian algebraic spaces
preserves coherence. -/
theorem isCoherent_le_inverseImage_pullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) :
    SheafOfModules.isCoherent (structureSheaf Y) ≤
      (SheafOfModules.isCoherent (structureSheaf X)).inverseImage
        (Modules.pullback f) :=
  sorry

namespace Coh

/-- Pullback of coherent modules along a morphism of locally Noetherian
algebraic spaces. -/
noncomputable def pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) :
    Coh Y ⥤ Coh X :=
  ObjectProperty.FullSubcategory.restrict (Modules.pullback f)
    (isCoherent_le_inverseImage_pullback f)

/-- The underlying module of a pulled-back coherent module is the ordinary
module pullback. -/
theorem pullback_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (M : Coh Y) :
    ((pullback f).obj M).obj = (Modules.pullback f).obj M.obj :=
  sorry

end Coh

/-- Stagewise pullback along `f` preserves the coherent-formal-system
conditions. -/
theorem isCoherentFormalModuleSystem_pullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (I : IdealSubobject Y)
    (F : SequentialInverseSystem (Coh Y))
    (hF : IsCoherentFormalModuleSystem I F) :
    IsCoherentFormalModuleSystem (I.pullback f) (F ⋙ Coh.pullback f) :=
  sorry

/-- The canonical functor sending a coherent formal module system to its
stagewise pullback along `f`. -/
noncomputable def coherentFormalModulesPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (I : IdealSubobject Y) :
    CoherentFormalModules Y I ⥤ CoherentFormalModules X (I.pullback f) :=
  (IsCoherentFormalModuleSystem (I.pullback f)).lift
    ((IsCoherentFormalModuleSystem I).ι ⋙
      (Functor.whiskeringRight ℕᵒᵖ (Coh Y) (Coh X)).obj (Coh.pullback f))
    (fun M ↦ isCoherentFormalModuleSystem_pullback f I M.obj M.property)

/-- Stagewise pullback of coherent formal modules preserves zero morphisms. -/
instance coherentFormalModulesPullback_preservesZeroMorphisms
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (I : IdealSubobject Y) :
    (coherentFormalModulesPullback f I).PreservesZeroMorphisms :=
  sorry

/-- Each stage of the canonical pullback functor is the ordinary module
pullback of the corresponding stage. -/
theorem coherentFormalModulesPullback_obj {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (I : IdealSubobject Y)
    (M : CoherentFormalModules Y I) (n : ℕ) :
    ((((coherentFormalModulesPullback f I).obj M).obj).obj (op n)).obj =
      (Modules.pullback f).obj (((M.obj).obj (op n)).obj) :=
  sorry

/-- Exactness of a short complex of coherent formal modules can be checked after
pullback along a surjective étale morphism of Noetherian algebraic spaces. -/
theorem coherentFormalModules_exact_iff_of_surjectiveEtale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsNoetherian X] [IsNoetherian Y]
    (I : IdealSubobject X) [IsQuasiCoherent I] (f : Y ⟶ X) [Etale f]
    [Surjective f] (C : ShortComplex (CoherentFormalModules X I)) :
    C.Exact ↔ (C.map (coherentFormalModulesPullback f I)).Exact :=
  sorry

/-- Stagewise pullback of coherent formal modules along a flat morphism of
Noetherian algebraic spaces is exact. -/
theorem coherentFormalModulesPullback_exact_of_flat {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Flat f] (I : IdealSubobject Y) [IsQuasiCoherent I] :
    exactFunctor (CoherentFormalModules Y I)
      (CoherentFormalModules X (I.pullback f))
      (coherentFormalModulesPullback f I) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
