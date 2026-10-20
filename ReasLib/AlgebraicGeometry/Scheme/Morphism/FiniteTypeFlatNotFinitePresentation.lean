/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace ProperFlatCounterexample

/-- There is a proper flat scheme morphism that is not finitely presented and whose fibers are
each either a projective line or the homogeneous coordinate-product closed subscheme of a
projective plane over the corresponding residue field. -/
theorem exists_nodalFibers :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S),
      Flat f ∧ IsProper f ∧ ¬Scheme.Hom.FinitePresentation f ∧
        ∀ s : S,
          Nonempty
              (Over.mk (f.fiberToSpecResidueField s) ≅
                Over.mk (ProjectiveSpace.toBase 1 (Spec (S.residueField s)))) ∨
            ∃ Z : (ProjectiveSpace.scheme (S.residueField s) 2).IdealSheafData,
              ProjectiveSpace.ClosedSubscheme.HasHomogeneousEquation 2 Z
                  (ProjectiveSpace.coordinate 2 1 * ProjectiveSpace.coordinate 2 2) ∧
                Nonempty
                  (Over.mk (f.fiberToSpecResidueField s) ≅
                    Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec (S.residueField s) 2)) := sorry

/-- There is a proper flat scheme morphism that is not finitely presented and whose fibers are
each either a projective line or a projective plane over the corresponding residue field. -/
theorem exists_projectiveFibers :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S),
      Flat f ∧ IsProper f ∧ ¬Scheme.Hom.FinitePresentation f ∧
        ∀ s : S,
          Nonempty
              (Over.mk (f.fiberToSpecResidueField s) ≅
                Over.mk (ProjectiveSpace.toBase 1 (Spec (S.residueField s)))) ∨
            Nonempty
              (Over.mk (f.fiberToSpecResidueField s) ≅
                Over.mk (ProjectiveSpace.toBase 2 (Spec (S.residueField s)))) := sorry

end ProperFlatCounterexample

end AlgebraicGeometry
