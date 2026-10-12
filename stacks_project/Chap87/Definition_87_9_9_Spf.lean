/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
public import stacks_project.Chap87.Definition_87_9_1_Affine

/-!
# Formal-spectrum compatibility

The shared owner supplies the formal spectrum and its quotient-stage diagram.
The affine-formal prerequisite remains available to existing consumers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spf :
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}},
    (Spec (.of A) ⟶ S) → ∀ [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    Sheaf (Scheme.fppfTopology.over S) (Type u))
