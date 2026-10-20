/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.ModuleSystem
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 52.16.2 (1): a finite-module inverse system satisfying the source
conditions gives a coherent formal module on `U`. -/
@[stacks 0DXT] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem.restrictedTilde_mem :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AlgebraicGeometry.AffineAlgebraizationSetup A)
      (M : AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem S),
      AlgebraicGeometry.Scheme.IsCoherentFormalModuleSystem
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)
        (M.restrictedTilde S))

/- Lemma 52.16.2 (2): every coherent formal module on `U` is realized by a
finite-module inverse system satisfying the source conditions. -/
@[stacks 0DXT] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem.exists_model :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AlgebraicGeometry.AffineAlgebraizationSetup A)
      (F : AlgebraicGeometry.Scheme.CoherentFormalModules S.U.toScheme
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)),
      ∃ M : AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem S,
        Nonempty (M.toFormalModule S ≅ F))
