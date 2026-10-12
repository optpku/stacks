/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import stacks_project.Chap69.Lemma_69_19_1
public import stacks_project.Chap69.Lemma_69_19_2
public import stacks_project.Chap69.Remark_69_19_3_Variant_for_complete_discrete_valuation_rings_CompleteDVR

/-!
# Remark 69.19.3

The Noetherian valuative criteria for morphisms of algebraic spaces still hold
when discrete valuation rings are replaced by complete discrete valuation rings,
or more generally by any extension-dense class of discrete valuation rings.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- Remark 69.19.3 (Variant for complete discrete valuation rings) (1): If
`f : X ⟶ Y` is a morphism of algebraic spaces over a scheme `S`, `Y` is locally
Noetherian, `f` is locally of finite type and quasi-separated, and every
complete DVR valuative square has at most one lift, then `f` is separated. -/
@[stacks 0ARL]
instance of_completeDvrUniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.CompleteDVR.Uniqueness f] : Separated f :=
  sorry

end Separated

namespace Proper

/-- Remark 69.19.3 (Variant for complete discrete valuation rings) (2): If
`f : X ⟶ Y` is a morphism of algebraic spaces over a scheme `S`, `Y` is locally
Noetherian, `f` is of finite type and quasi-separated, and every complete DVR
valuative square admits an extension `A ⊂ A'` of complete discrete valuation
rings with a unique arrow `Spec(A') ⟶ X`, then `f` is proper. -/
@[stacks 0ARL]
instance of_completeDvr {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [FiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.CompleteDVR.Existence f] : Proper f :=
  sorry

end Proper

namespace ValuativeCriterion.DVR.Uniqueness

/-- Remark 69.19.3 (Variant for complete discrete valuation rings) (3): If `P` is
an extension-dense class of discrete valuation rings and every valuative square
whose ring lies in `P` has at most one lift, then `f` satisfies DVR uniqueness. -/
@[stacks 0ARL]
theorem of_extensionDense
    {P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop}
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.ExtensionDense P]
    (h : ∀ (sq : ValuativeCommSq f) [IsDiscreteValuationRing sq.R],
      P sq.R → Subsingleton sq.commSq.LiftStruct) :
    Uniqueness f :=
  sorry

end ValuativeCriterion.DVR.Uniqueness

namespace ValuativeCriterion.DVR.Existence

/-- Remark 69.19.3 (Variant for complete discrete valuation rings) (4): If `f` is
separated and `P` is an extension-dense class of discrete valuation rings such
that every valuative square whose ring lies in `P` admits a `P`-valued
extension with a lift, then `f` satisfies DVR existence. -/
@[stacks 0ARL]
theorem of_extensionDense
    {P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop}
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [ValuativeCriterion.DVR.ExtensionDense P]
    (h : ∀ (sq : ValuativeCommSq f) [IsDiscreteValuationRing sq.R],
      P sq.R → ∃ (e : sq.Extension) (hR' : IsDiscreteValuationRing e.R'), P e.R') :
    Existence f :=
  sorry

end ValuativeCriterion.DVR.Existence

namespace ValuativeCriterion.DVR.ExtensionDense

/-- Remark 69.19.3 (Variant for complete discrete valuation rings) (5): Complete
discrete valuation rings with algebraically closed residue field form an
extension-dense class of discrete valuation rings. -/
@[stacks 0ARL]
instance completeAlgClosedResidue :
    ExtensionDense fun (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] ↦
      IsCompleteLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) :=
  sorry

end ValuativeCriterion.DVR.ExtensionDense

end AlgebraicGeometry.AlgebraicSpace
