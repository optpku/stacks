/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing.Adjunction
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic

/-!
# Equivalence for formal glueing of quasi-coherent modules

The canonical glueing functor is an equivalence with the reverse kernel functor
as quasi-inverse, and its canonical unit and counit are isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- The canonical unit from a quasi-coherent module to its reverse glueing
kernel is an isomorphism under the formal-glueing hypotheses. -/
instance unit_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    IsIso (unit f i) := sorry

/-- The canonical counit from the glueing of a reverse kernel to the original
glueing triple is an isomorphism under the formal-glueing hypotheses. -/
instance counit_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    IsIso (counit f i) := sorry

/-- The reverse signed-comparison kernel functor is a quasi-inverse of the
canonical glueing functor under the formal-glueing hypotheses. -/
@[stacks 0AF0]
theorem reverse_isQuasiInverse {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (functor f i).IsQuasiInverse (reverse f i) := sorry

/-- The canonical restriction and pullback functor to quasi-coherent glueing
triples is an equivalence under the formal-glueing hypotheses. -/
@[stacks 0AF0, instance]
instance functor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (functor f i).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing
