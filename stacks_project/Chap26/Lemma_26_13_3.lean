/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.13.3 (1): for a scheme `X` and a field `K`, a morphism `Spec K ⟶ X`
corresponds to a point `x : X` together with a morphism `κ(x) ⟶ K`. -/
@[stacks 01J9] #check Scheme.SpecToEquivOfField

/- Lemma 26.13.3 (2): every morphism `f : Spec K ⟶ X` factors through the canonical
map `Spec κ(x) ⟶ X` attached to the image `x` of the unique point of `Spec K`. -/
@[stacks 01J9] #check Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField

/- ReasLib companions: class-level classification, smallest representatives, and their
uniqueness are exposed by the shared field-valued-point owner. -/
#check Scheme.FieldValuedPoint.classesEquiv
#check Scheme.FieldValuedPoint.residuePoint_isSmallest
#check Scheme.FieldValuedPoint.iso_unique_of_isSmallest

/- ReasLib companions expose the categorical terminal-object form of uniqueness. -/

#check Scheme.FieldValuedPoint.homMk
#check Scheme.FieldValuedPoint.fieldHom
#check Scheme.FieldValuedPoint.fieldHom.specMap
#check Scheme.FieldValuedPoint.toOverFullyFaithful
#check Scheme.FieldValuedPoint.mapFunctor
#check Scheme.FieldValuedPoint.mapFunctor_faithful
#check Scheme.FieldValuedPoint.mapFunctor.comp_toOver
#check Scheme.FieldValuedPoint.mapFunctor.mapId_eq
#check Scheme.FieldValuedPoint.mapFunctor.mapComp_eq
#check Scheme.FieldValuedPoint.Factorization.map
#check Scheme.FieldValuedPoint.Factorization.map_hom
#check Scheme.FieldValuedPoint.factorToResiduePoint
#check Scheme.FieldValuedPoint.factorToResiduePoint.map
#check Scheme.FieldValuedPoint.residuePoint.mapFactor
#check Scheme.FieldValuedPoint.CommonExtension.point
#check Scheme.FieldValuedPoint.CommonExtension.left
#check Scheme.FieldValuedPoint.CommonExtension.right
#check Scheme.FieldValuedPoint.CommonExtension.map_point
#check Scheme.FieldValuedPoint.CommonExtension.map_left
#check Scheme.FieldValuedPoint.CommonExtension.map_right
#check Scheme.FieldValuedPoint.equivalent_iff_zigzag
#check Scheme.FieldValuedPoint.connectedComponents_mk_eq_iff
#check CategoryTheory.Functor.mapConnectedComponents
#check CategoryTheory.Functor.mapConnectedComponents_mk
#check Scheme.FieldValuedPoint.residuePoint_isTerminal
#check Scheme.FieldValuedPoint.isTerminalRepresentative_iff
#check Scheme.FieldValuedPoint.classesEquiv_naturality
