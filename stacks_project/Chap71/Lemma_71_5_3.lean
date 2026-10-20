/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Support
import StacksCheckRecall

/-!
# Lemma 71.5.3

The scheme-theoretic support of a finite-type quasi-coherent module on an
algebraic space is contained in the closed subspace cut out by the zeroth
Fitting ideal, both have underlying set the ordinary support, and the module
descends to a finite-type quasi-coherent module on that Fitting closed
subspace.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.5.3 (1): the scheme-theoretic support factors through the zeroth
Fitting closed subspace. -/
@[stacks 0CZ6] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.schemeTheoreticSupport_le_fittingIdealZeroSubspace :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      {Z : AlgebraicSpace S} (i : Z ⟶ X) [IsSchemeTheoreticSupport F i],
      ∃ f : Z ⟶ (fittingIdealZeroSubspace F).X,
        f ≫ (fittingIdealZeroSubspace F).ι = i)

/- Lemma 71.5.3 (2): both closed subspaces have underlying point-set equal to
ordinary module support. -/
@[stacks 0CZ6] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.fittingIdealZeroSubspace_pointsSet_eq_moduleSupport :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      {Z : AlgebraicSpace S} (i : Z ⟶ X) [IsSchemeTheoreticSupport F i],
      Set.range (Points.map i) = (fittingIdealZeroSubspace F).pointsSet ∧
        (fittingIdealZeroSubspace F).pointsSet = moduleSupport F)

/- Lemma 71.5.3 (3): the module descends to a finite-type quasi-coherent module
on the zeroth Fitting closed subspace. -/
@[stacks 0CZ6] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_finiteType_module_pushforward_fittingIdealZero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      ∃ G0 : (fittingIdealZeroSubspace F).X.Modules,
        G0.IsQuasicoherent ∧ G0.IsFiniteType ∧
          Nonempty ((pushforward (fittingIdealZeroSubspace F).ι).obj G0 ≅ F))
