/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.NormalizationVectorFields

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Hom
open SheafOfModules

noncomputable section

universe u

/- Lemma 53.26.2 (1): Derivations descend through normalization exactly when they fix every exceptional point. -/
@[stacks 0E68] #check (AlgebraicGeometry.Curve.normalizationDerivation_range :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules)),
    (∃ D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules),
      AlgebraicGeometry.Curve.normalizationDerivationExtends X D D') ↔
      ∀ xν ∈ AlgebraicGeometry.Curve.normalizationExceptionalPoints X,
        AlgebraicGeometry.Curve.derivationFixesAt
          (SchemeOverField.normalization X) D' xν)

/- Lemma 53.26.2 (2): Derivations on the curve lift uniquely to compatible derivations on the normalization. -/
@[stacks 0E68]
#check (AlgebraicGeometry.Curve.normalizationDerivation_lift_existsUnique :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)),
    ∃! D' : derivations (SchemeOverField.normalization X).hom.toShHom
      (SheafOfModules.unit
        (SchemeOverField.normalization X).left.ringCatSheaf :
        (SchemeOverField.normalization X).left.Modules),
      AlgebraicGeometry.Curve.normalizationDerivationExtends X D D')
