/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ProjectionFormula
public import stacks_project.Chap36.Lemma_36_4_5
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived.ProjectionFormula

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]

/- Lemma 36.22.1: for a quasi-compact and quasi-separated morphism of schemes,
the canonical map `Rf_* E ⊗ᴸ K ⟶ Rf_* (E ⊗ᴸ Lf^* K)` is an isomorphism when
`E` and `K` have quasi-coherent cohomology. -/
@[stacks 08EU] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.isIso_projectionFormula f :
    ∀ (E : DerivedQCoh X) (K : DerivedQCoh Y),
      IsIso (leftMate f.toShHom E.obj K.obj))

end AlgebraicGeometry.Scheme.DerivedQCoh
