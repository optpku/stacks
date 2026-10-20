module

public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap76.«76_42_2_1_Category»

/-!
# Pullback of coherent formal modules along morphisms of algebraic spaces

Stagewise module pullback lifts to a functor
`CoherentFormalModules Y I ⥤ CoherentFormalModules X (I.pullback f)`
on the 08B4 category of coherent formal modules.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

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
def pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
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
    (f : X ⟶ Y) (I : IdealSubobject Y) [IsQuasiCoherent I]
    (F : SequentialInverseSystem (Coh Y))
    (hF : IsCoherentFormalModuleSystem I F) :
    IsCoherentFormalModuleSystem (I.pullback f) (F ⋙ Coh.pullback f) :=
  sorry

/-- The canonical functor sending a coherent formal module system to its
stagewise pullback along `f`. -/
def coherentFormalModulesPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (I : IdealSubobject Y) [IsQuasiCoherent I] :
    CoherentFormalModules Y I ⥤ CoherentFormalModules X (I.pullback f) :=
  (IsCoherentFormalModuleSystem (I.pullback f)).lift
    ((IsCoherentFormalModuleSystem I).ι ⋙
      (Functor.whiskeringRight ℕᵒᵖ (Coh Y) (Coh X)).obj (Coh.pullback f))
    (fun M ↦ isCoherentFormalModuleSystem_pullback f I M.obj M.property)

/-- Each stage of the canonical pullback functor is the ordinary module
pullback of the corresponding stage. -/
theorem coherentFormalModulesPullback_obj {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (I : IdealSubobject Y) [IsQuasiCoherent I]
    (M : CoherentFormalModules Y I) (n : ℕ) :
    ((((coherentFormalModulesPullback f I).obj M).obj).obj (op n)).obj =
      (Modules.pullback f).obj (((M.obj).obj (op n)).obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
