module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.CompleteDVR.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.CompleteDVR.Proper

/-!
# Remark 69.19.3

The Noetherian valuative criteria for morphisms of algebraic spaces suffice when
tested on complete discrete valuation rings. More generally, any extension-dense
class of discrete valuation rings suffices, including complete DVRs with
algebraically closed residue field.

In the existence hypotheses, `ValuativeCommSq.Extension` already stores a lift
of the extended square, a dominating ring extension, compatible fraction-field
algebras, and scalar towers. Thus the complete-DVR existence condition requires
an actual unique lift after an extension of complete DVRs.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 69.19.3 (Variant for complete discrete valuation rings)
(1) Uniqueness on complete DVR squares implies separatedness under the
Noetherian finiteness hypotheses. -/
@[stacks 0ARL] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated.of_completeDvrUniqueness :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsLocallyNoetherian Y] → [LocallyOfFiniteType f] → [QuasiSeparated f] →
      [ValuativeCriterion.CompleteDVR.Uniqueness f] → Separated f)

/- (2) A unique lift after a complete-DVR extension implies properness under
the Noetherian finiteness hypotheses; separatedness is a consequence. -/
#check (AlgebraicGeometry.AlgebraicSpace.Proper.of_completeDvr :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsLocallyNoetherian Y] → [FiniteType f] → [QuasiSeparated f] →
    [ValuativeCriterion.CompleteDVR.Existence f] → Proper f)

/- (3) Uniqueness can be tested on any extension-dense class of DVRs. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Uniqueness.of_extensionDense :
  ∀ {P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop}
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsDiscreteValuationRing.ExtensionDense P] →
    (∀ (sq : ValuativeCommSq f) [IsDiscreteValuationRing sq.R],
      P sq.R → Subsingleton sq.commSq.LiftStruct) →
    ValuativeCriterion.DVR.Uniqueness f)

/- (4) For a separated morphism, existence follows from lifts after extensions
within an extension-dense class. The extension itself supplies the lift. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence.of_extensionDense :
  ∀ {P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop}
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [Separated f] → [IsDiscreteValuationRing.ExtensionDense P] →
    (∀ (sq : ValuativeCommSq f) [IsDiscreteValuationRing sq.R],
      P sq.R → ∃ (e : sq.Extension) (hR' : IsDiscreteValuationRing e.R'), P e.R') →
    ValuativeCriterion.DVR.Existence f)

/- (5) Complete DVRs with algebraically closed residue field are extension-dense. -/
#check (IsDiscreteValuationRing.ExtensionDense.completeAlgClosedResidue :
  IsDiscreteValuationRing.ExtensionDense
    fun (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] ↦
      IsCompleteLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R))
