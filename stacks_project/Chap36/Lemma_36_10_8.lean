/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Finiteness
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalClosed
open Functor.PullbackInternalHom.Left
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open Opposite TopologicalSpace

noncomputable section

universe u

/- Lemma 36.10.8 (1): derived internal Hom from a pseudo-coherent complex to a
bounded-below complex with quasi-coherent cohomology again has quasi-coherent cohomology. -/
@[stacks 0A6H]
#check (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.derivedQCoh_of_pseudoCoherent :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
    (K : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
    (L : AlgebraicGeometry.Scheme.DerivedQCoh X)
    (hK : AlgebraicGeometry.Scheme.IsPseudoCoherent X K)
    (hL : (t.plus : ObjectProperty
      (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)) L.obj),
    AlgebraicGeometry.Scheme.derivedQuasiCoherentModuleProperty X
      ((ihomOf H K).obj L.obj))

/- Clause (2): the same derived internal Hom is locally bounded below. -/
#check (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.locallyBoundedBelow_of_pseudoCoherent :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
    (K : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
    (L : AlgebraicGeometry.Scheme.DerivedQCoh X)
    (hK : AlgebraicGeometry.Scheme.IsPseudoCoherent X K)
    (hL : (t.plus : ObjectProperty
      (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)) L.obj),
    AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyBoundedBelow
      ((ihomOf H K).obj L.obj))

/- Clause (3): a perfect source preserves quasi-coherent cohomology without a boundedness
assumption on the target. -/
#check (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.derivedQCoh_of_perfect :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
    (K : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
    (L : AlgebraicGeometry.Scheme.DerivedQCoh X)
    (hK : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect K),
    AlgebraicGeometry.Scheme.derivedQuasiCoherentModuleProperty X
      ((ihomOf H K).obj L.obj))

/- Clause (4): on an affine scheme, the tilde/internal-Hom comparison is invertible for a
pseudo-coherent source and bounded-below target. -/
#check (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineComparison_isIso_of_pseudoCoherent :
  ∀ {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [KFlat.HomotopyTensorDescends
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace))
    (T : Functor.TensorComparison
      (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : K.IsPseudoCoherent) (hL : DerivedCategory.IsBoundedBelow L),
    IsIso (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineComparison
      M H T K L))

/- Clause (5): on an affine scheme, the tilde/internal-Hom comparison is invertible for a
perfect source and arbitrary target. -/
#check (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineComparison_isIso_of_perfect :
  ∀ {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [KFlat.HomotopyTensorDescends
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace))
    (T : Functor.TensorComparison
      (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (hK : K.IsPerfect),
    IsIso (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineComparison
      M H T K L))

/- Clause (6): affine internal-Hom cohomology is the sheafification of the presheaf of
localized Ext groups on principal opens. -/
#check (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineInternalHomCohomologySheaf_isomorphic_affineExtSheaf :
  ∀ {A : Type u} [CommRing A]
    [HasWeakSheafify (Opens.grothendieckTopology (PrimeSpectrum A))
      AddCommGrpCat.{u + 1}]
    [KFlat.HomotopyTensorDescends
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace]
    (H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived
      (AlgebraicGeometry.Spec (CommRingCat.of A)).toRingedSpace))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ),
    IsIsomorphic
      (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineInternalHomCohomologySheaf
        H K L n)
      (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.affineExtSheaf K L n))
