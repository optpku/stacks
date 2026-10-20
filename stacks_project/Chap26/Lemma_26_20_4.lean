/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Valuation
import StacksCheckRecall

@[expose] public section

/- Lemma 26.20.4 (1): a scheme specialization is realized by the generic and closed points of the
spectrum of a valuation ring. -/
@[stacks 01J8] #check _root_.Specializes.exists_valuationRing_morphism_basic

/- Lemma 26.20.4 (2): the realization can use a prescribed extension of the residue field of the
general point as its fraction field. -/
@[stacks 01J8] #check _root_.Specializes.exists_valuationRing_morphism

#check _root_.Specializes.ValuationRealization
#check _root_.Specializes.ValuationRealization.cast
#check _root_.Specializes.ValuationRealization.cast_rfl
#check _root_.Specializes.ValuationRealization.residueFieldMap
#check _root_.Specializes.ValuationRealization.genericSq
#check _root_.Specializes.ValuationRealization.genericMap
#check _root_.Specializes.ValuationRealization.genericMap_eq
#check _root_.Specializes.ValuationRealization.toValuativeCommSq
#check _root_.Specializes.ValuationRealization.map_genericPoint
#check _root_.Specializes.ValuationRealization.spec
#check _root_.Specializes.ValuationRealization.specializes
#check _root_.Specializes.ValuationRealization.nonempty
#check _root_.Specializes.ValuationRealization.nonempty_iff_specializes
#check _root_.Specializes.map_genericPoint_of_fractionSq
