/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.EulerCharacteristic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.Hom Scheme.Modules
open Scheme.DerivedQCoh
open ProperDualizingComplex

noncomputable section

universe u

/- Lemma 53.5.1 (1) -/
@[stacks 0BS5] #check
  (AlgebraicGeometry.Scheme.Hom.structureSheafEulerCharacteristic_eq :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [IsProper X.hom] (h_dimension : topologicalKrullDim X.left ≤ 1),
      let _ :
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules).IsCoherent :=
        @structureSheaf_isCoherent X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      eulerCharacteristic X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) =
        AlgebraicGeometry.Scheme.Hom.derivedEulerCharacteristic X.hom
          (properDualizingComplex X.hom))

/- Lemma 53.5.1 (2) -/
@[stacks 0BS5] #check
  (AlgebraicGeometry.Scheme.Hom.structureSheafEulerCharacteristic_eq_neg_curveModule :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [IsProper X.hom] [AlgebraicGeometry.Scheme.CohenMacaulay X.left]
      [TopologicalSpace.EquidimensionalSpace X.left]
      (h_dimension : topologicalKrullDim X.left = 1),
      let _ :
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules).IsCoherent :=
        @structureSheaf_isCoherent X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      let _ : (curveDualizingModule X.hom).IsCoherent :=
        curveDualizingModule_isCoherent X h_dimension.le
      eulerCharacteristic X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) =
        -eulerCharacteristic X.hom (curveDualizingModule X.hom))
