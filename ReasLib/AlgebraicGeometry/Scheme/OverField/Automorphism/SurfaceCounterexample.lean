/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Automorphism

/-!
# Infinite discrete automorphism groups of surfaces
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- There is a smooth projective proper integral surface over an algebraically closed field
with trivial canonical module, vanishing first structure-sheaf cohomology, and infinitely
many automorphisms, whose automorphism functor is represented by a locally finite type
scheme with discrete topology and dimension zero. -/
theorem exists_k3_infiniteDiscreteAutomorphismGroup :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (X : SchemeOverField k)
      (_ : Projective X.hom) (_ : IsProper X.hom) (_ : Smooth X.hom)
      (_ : IsIntegral X.left)
      (hdim : topologicalKrullDim X.left = 2)
      (hcanonical : Nonempty
        (dualizingModule X.hom ≅
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))
      (hH1 : IsZero
        (Hom.cohomology X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)),
      Infinite (Aut X) ∧
        (∃ (G : SchemeOverField k)
          (_ : (autFunctor X ⋙ forget GrpCat).RepresentableBy G),
          LocallyOfFiniteType G.hom ∧ DiscreteTopology G.left ∧
            topologicalKrullDim G.left = 0) := sorry

end AlgebraicGeometry.SchemeOverField
