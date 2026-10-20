/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationDescent
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
  CategoryTheory.Limits Opposite

universe u

/- Remark 66.18.4: the extension of a small étale sheaf is computed by the
 equalizer associated to a surjective étale scheme presentation. -/
@[stacks 03H7] #check (AlgebraicGeometry.AlgebraicSpace.isIso_spacesEtaleExtension_toEqualizer :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left),
    IsIso (spacesEtaleExtension_toEqualizer F π fst snd hπ h_pair))

#check (AlgebraicGeometry.AlgebraicSpace.unique_spacesEtaleExtension :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1))),
    Nonempty ((smallEtalePresentationRestriction X).obj G ≅ F) ↔
      Nonempty (G ≅ (smallEtalePresentationExtension X).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.smallEtalePresentationCounitIso :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    smallEtalePresentationExtension X ⋙ smallEtalePresentationRestriction X ≅
      𝟭 (Sheaf (smallEtaleTopology X) (Type (u + 1))))

#check (AlgebraicGeometry.AlgebraicSpace.exists_surjectiveEtaleSchemeCover :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U : spacesEtaleSite X),
    ∃ (U' : smallEtaleSite X) (π : (smallEtaleToSpaces X).obj U' ⟶ U),
      Representable.Etale π.left ∧ Function.Surjective (Points.map π.left))

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_schemeCover_mem_spacesEtalePrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U)
    (hπ : Function.Surjective (Points.map π.left)),
    Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ (smallEtaleToSpaces X).obj U') (fun _ ↦ π) ∈
      spacesEtalePrecoverage X U)

#check (AlgebraicGeometry.AlgebraicSpace.exists_kernelPair_of_isEtaleFromScheme :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleToSpaces X).obj U' ⟶ U) (hp : Representable.Etale π.left),
    ∃ (R : smallEtaleSite X) (fst snd : R ⟶ U'),
      IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left)
