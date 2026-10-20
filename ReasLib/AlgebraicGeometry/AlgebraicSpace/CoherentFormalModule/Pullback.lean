module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Category

/-!
# Pullback and exactness of coherent formal modules
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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
