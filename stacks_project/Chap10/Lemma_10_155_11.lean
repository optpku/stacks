/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Presentation.PointedEtale
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.Localization.AtPrime.SeparableClosure
import StacksCheckRecall

@[expose] public section

/-!
# Strict etale neighborhoods over a separable closure

The reusable pointed-etale presentation owner is
`IsStrictHenselizationOf.PointedEtale`.  This source-facing file recalls the
three claims of Lemma 10.155.11 through the shared API.  The selected target's
kernel equality is the generic scalar-tower fact in `Ideal.ResidueField`, and
the source's residue-field identification is represented by
`PointedEtale.Coordinate`, rather than by a chapter-local pair of maps and
compatibility aliases.

@stack 04GW
-/

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

noncomputable section

namespace Chap10

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]
variable {Ksep : Type u} [Field Ksep]
variable [Algebra R Ksep]
variable [Algebra p.ResidueField Ksep]
variable [IsScalarTower R p.ResidueField Ksep]
variable [IsSepClosure p.ResidueField Ksep]

/- The chosen separable-closure target has kernel `p`; this is exactly the
generic scalar-tower theorem at the present source data. -/
@[stacks 04GW "kernel of the separable-closure target map"]
#check (Ideal.ResidueField.ker_algebraMap_eq_of_scalarTower
  (R := R) (p := p) (K := Ksep) : RingHom.ker (algebraMap R Ksep) = p)
#check @Localization.AtPrime.residueMapOfAlgebra
#check @Localization.AtPrime.residueMapOfAlgebra_isSepClosure

/- Lemma 10.155.11 (1), tag `04GW`: the category of triples `(S, q, φ)` with
`R → S` etale, `q` over `p`, and `φ : κ(q) → Ksep` a `κ(p)`-algebra map is
filtered.  The canonical pointed-etale category is the shared owner. -/
@[stacks 04GW]
#check (CommAlgCat.Over.Etale.isFiltered (R := R) (T := Ksep) :
  IsFiltered (CommAlgCat.Over.Etale.category R Ksep))

/- Lemma 10.155.11 (2), tag `04GW`: the source diagram
`(S, q, φ) ↦ S` has the chosen strict henselization as a colimit.  The
source cocone and its colimit assertion are owned by the generic pointed-etale
presentation API. -/
@[stacks 04GW]
#check @IsStrictHenselizationOf.PointedEtale.Presentation.sourceCocone
@[stacks 04GW]
#check @IsStrictHenselizationOf.PointedEtale.Presentation.sourceIsColimit

/- Lemma 10.155.11 (3), tag `04GW`: the localized diagram
`(S, q, φ) ↦ S_q` has the chosen strict henselization as a colimit.  The
localized cocone and its Prop-valued colimit assertion are shared directly. -/
@[stacks 04GW]
#check @IsStrictHenselizationOf.PointedEtale.Presentation.cocone
@[stacks 04GW]
#check @IsStrictHenselizationOf.PointedEtale.Presentation.isColimit

end Chap10
