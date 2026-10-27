/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Complex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.DirectSum.Basic

/-!
# Derived Chern operations by the fixed family of all envelope models

Instead of choosing a Chern-class family satisfying a predicate, form the
direct sum of Chow groups of all genuine envelope/finite-free models. Its
specified map is the sum of proper pushforwards. The operation on each
summand is the actual complex Chern/Newton operation followed by pushforward.
Descent through this fixed map defines the derived operation. Existence of
an envelope representative supplies a base-changed model and residue-field
lifts of cycle points. These give an explicit preimage of each Chow class;
only the right-inverse and descent laws are used as proof fields.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DirectSum
noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern.EnvelopeCaps

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
  {X : Over S} [LocallyOfFiniteType X.hom] (classes : ChernClass.Theory δ X.hom)
  (E : RingedSpace.ModuleDerived X.left.toRingedSpace)

/-- An envelope presentation of a pullback of a perfect derived module by a locally
bounded complex of finite locally free modules. -/
structure Model (V : Over S) (g : V ⟶ X) : Type (u + 1) where
  Y : Over S
  finiteType : LocallyOfFiniteType Y.hom
  map : Y ⟶ V
  envelope : IsEnvelope map.left
  complex : CochainComplex Y.left.Modules ℤ
  represents : IsIsomorphic (DerivedCategory.Q.obj complex)
    ((RingedSpace.modulePullbackDerived (map ≫ g).left.toShHom).obj E)
  above : RingedSpace.CochainComplex.IsLocallyBoundedAbove complex
  below : RingedSpace.CochainComplex.IsLocallyBoundedBelow complex
  free : ∀ n, Scheme.Modules.IsFiniteLocallyFree (complex.X n)

/-- An envelope and a locally bounded finite locally free representative of the pulled-back
derived module determine an explicit envelope model. -/
def Model.ofRepresentative {V : Over S} (g : V ⟶ X)
    (Y : Over S) [LocallyOfFiniteType Y.hom] (map : Y ⟶ V)
    (envelope : IsEnvelope map.left) (complex : CochainComplex Y.left.Modules ℤ)
    (represents : IsIsomorphic (DerivedCategory.Q.obj complex)
      ((RingedSpace.modulePullbackDerived (map ≫ g).left.toShHom).obj E))
    (above : RingedSpace.CochainComplex.IsLocallyBoundedAbove complex)
    (below : RingedSpace.CochainComplex.IsLocallyBoundedBelow complex)
    (free : ∀ n, Scheme.Modules.IsFiniteLocallyFree (complex.X n)) : Model E V g where
  Y := Y
  finiteType := inferInstance
  map := map
  envelope := envelope
  complex := complex
  represents := represents
  above := above
  below := below
  free := free

/-- The model constructed from an envelope representative has an envelope map and a
representative that is locally bounded in both directions and termwise finite locally free. -/
theorem Model.ofRepresentative_spec {V : Over S} (g : V ⟶ X)
    (Y : Over S) [LocallyOfFiniteType Y.hom] (map : Y ⟶ V)
    (envelope : IsEnvelope map.left) (complex : CochainComplex Y.left.Modules ℤ)
    (represents : IsIsomorphic (DerivedCategory.Q.obj complex)
      ((RingedSpace.modulePullbackDerived (map ≫ g).left.toShHom).obj E))
    (above : RingedSpace.CochainComplex.IsLocallyBoundedAbove complex)
    (below : RingedSpace.CochainComplex.IsLocallyBoundedBelow complex)
    (free : ∀ n, Scheme.Modules.IsFiniteLocallyFree (complex.X n)) :
    let model := Model.ofRepresentative E g Y map envelope complex represents above below free
    IsEnvelope model.map.left ∧
      IsIsomorphic (DerivedCategory.Q.obj model.complex)
        ((RingedSpace.modulePullbackDerived (model.map ≫ g).left.toShHom).obj E) ∧
      RingedSpace.CochainComplex.IsLocallyBoundedAbove model.complex ∧
      RingedSpace.CochainComplex.IsLocallyBoundedBelow model.complex ∧
      ∀ n, Scheme.Modules.IsFiniteLocallyFree (model.complex.X n) := sorry

variable {V : Over S} [LocallyOfFiniteType V.hom] (g : V ⟶ X)

/-- The relative Chow group attached to the source of an envelope model. -/
abbrev ModelChow (k : ℤ) (m : Model E V g) :=
  @RelativeChow S _ δ _ m.Y m.finiteType k

/-- The homomorphism from the direct sum over envelope models obtained by summing their
proper pushforwards. -/
def coverMap (k : ℤ) : (⨁ m : Model E V g, ModelChow δ E g k m) →+ RelativeChow δ V k :=
  -- Local instance justification (noncanonical choice): direct sums require decidable model equality.
  letI := Classical.decEq (Model E V g)
  DirectSum.toAddMonoid fun m =>
    @ChowGroup.map S _ δ _ m.Y V m.finiteType _ m.map m.envelope.toIsProper k

/-- The degree-`q` Chern operation of an envelope representative; `rankBound = true`
selects the total Chern class and `rankBound = false` selects the Newton class. -/
def modelClass (rankBound : Bool) (q : ℕ) (m : Model E V g) :
    @BivariantClass _ _ δ _ m.Y m.Y m.finiteType m.finiteType (𝟙 m.Y) (q : ℤ) :=
  -- Local instance justification (defeq pin): use the finite-type evidence stored by this model.
  letI := m.finiteType
  if rankBound then
      ChernClass.Complex.totalClass δ m.Y.hom (classes.reanchor m.Y)
        m.complex m.above m.below m.free q
    else
      ChernClass.Complex.newtonClass δ m.Y.hom (classes.reanchor m.Y)
        m.complex m.above m.below m.free q

/-- The sum of the model-wise Chern operations followed by proper pushforward, before
descent to the target Chow group. -/
def beforeDescent (rankBound : Bool) (q : ℕ) (k : ℤ) :
    (⨁ m : Model E V g, ModelChow δ E g k m) →+ RelativeChow δ V (k - (q : ℤ)) :=
  -- Local instance justification (noncanonical choice): direct sums require decidable model equality.
  letI := Classical.decEq (Model E V g)
  DirectSum.toAddMonoid fun m =>
    -- Local instance justification (defeq pin): align cap with this model's stored evidence.
    letI := m.finiteType
    (@ChowGroup.map S _ δ _ m.Y V m.finiteType _ m.map m.envelope.toIsProper
      (k - (q : ℤ))).comp
      ((modelClass (δ := δ) (classes := classes) (E := E) (g := g)
        rankBound q m).cap (𝟙 m.Y) (𝟙 m.Y) (𝟙 m.Y)
        IsPullback.of_id_snd k)

variable (perfect : RingedSpace.ModuleDerived.IsPerfect E)
  (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ X.left), IsEnvelope f ∧
    RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((RingedSpace.modulePullbackDerived f.toShHom).obj E))

/-- The completely decomposed part of base change is constructed from the input
residue-field lifts, rather than an admitted existence theorem. -/
theorem envelope_pullback {Y Z T : Scheme.{u}} (f : Y ⟶ Z)
    (hf : IsEnvelope f) (a : T ⟶ Z) : IsEnvelope (pullback.snd f a) := by
  letI := hf.toIsProper
  refine { toIsProper := inferInstance, toCompletelyDecomposedFamily := ?_ }
  constructor
  intro x
  rcases hf.toCompletelyDecomposedFamily.exists_lift (a x) with ⟨i, s, hs⟩
  have comm : (Spec.map (a.residueFieldMap x) ≫ s) ≫ f =
      T.fromSpecResidueField x ≫ a := by
    rw [Category.assoc, hs]
    exact a.SpecMap_residueFieldMap_fromSpecResidueField x
  exact ⟨PUnit.unit, pullback.lift (Spec.map (a.residueFieldMap x) ≫ s)
    (T.fromSpecResidueField x) comm, pullback.lift_snd _ _ _⟩

/-- Pull back the actual envelope and complex supplied by definedness. The choices
here unpack the input hypothesis, not a new existential theorem. -/
def Model.ofDefined : Model E V g := by
  classical
  let Y := defined.choose
  let f : Y ⟶ X.left := defined.choose_spec.choose
  have hf : IsEnvelope f := defined.choose_spec.choose_spec.1
  let K := defined.choose_spec.choose_spec.2.choose
  have hK := defined.choose_spec.choose_spec.2.choose_spec
  letI := hf.toIsProper
  exact
    { Y := Over.mk (pullback.snd f g.left ≫ V.hom)
      finiteType := inferInstance
      map := Over.homMk (pullback.snd f g.left)
      envelope := envelope_pullback f hf g.left
      complex := ChernClass.Complex.pullbackComplex (pullback.fst f g.left) K
      represents := by
        -- Compatibility of termwise pullback with derived pullback and composition.
        sorry
      above := ChernClass.Complex.pullbackComplex_isLocallyBoundedAbove _ K hK.2.1
      below := ChernClass.Complex.pullbackComplex_isLocallyBoundedBelow _ K hK.2.2.1
      free := ChernClass.Complex.pullbackComplex_isFiniteLocallyFree _ K hK.2.2.2 }

/-- Choose a residue-field lift already present in the envelope's defining hypothesis
and take its unique source point. -/
def Model.liftPoint (m : Model E V g) (x : V.left) : m.Y.left :=
  (m.envelope.toCompletelyDecomposedFamily.exists_lift x).choose_spec.choose
    (IsLocalRing.closedPoint (V.left.residueField x))

/-- The selected point lies over the input point. -/
theorem Model.map_liftPoint (m : Model E V g) (x : V.left) :
    m.map.left (Model.liftPoint E g m x) = x := by
  have hs := (m.envelope.toCompletelyDecomposedFamily.exists_lift x).choose_spec.choose_spec
  change (((m.envelope.toCompletelyDecomposedFamily.exists_lift x).choose_spec.choose) ≫
    m.map.left) (IsLocalRing.closedPoint (V.left.residueField x)) = x
  rw [hs]
  exact V.left.fromSpecResidueField_apply x _

/-- A residue-field lift has the same relative dimension as the input point. -/
theorem Model.liftPoint_dimension (m : Model E V g) (x : V.left) :
    @Scheme.Hom.relativeDimensionFunction _ _ m.Y.hom m.finiteType δ
        (Model.liftPoint E g m x) =
      V.hom.relativeDimensionFunction δ x := sorry

/-- Put the original coefficient at the selected point of each fibre and zero at all
other points. This is the cycle lift used in envelope Chow generation. -/
def Model.liftCoefficients (m : Model E V g) (k : ℤ)
    (α : CycleGroup V.left (V.hom.relativeDimensionFunction δ) k) (y : m.Y.left) : ℤ := by
  classical
  exact if Model.liftPoint E g m (m.map.left y) = y then α.1 (m.map.left y) else 0

/-- The coefficient lift has locally finite support: on a lifted neighbourhood its
support is contained in the image of the original finite support. -/
theorem Model.liftCoefficients_locallyFinite (m : Model E V g) (k : ℤ)
    (α : CycleGroup V.left (V.hom.relativeDimensionFunction δ) k) :
    LocallyFiniteSupport (Model.liftCoefficients δ E g m k α) := by
  classical
  intro y
  obtain ⟨t, ht, hfinite⟩ := α.1.locallyFiniteSupport (m.map.left y)
  refine ⟨m.map.left ⁻¹' t, m.map.left.continuous.continuousAt.preimage_mem_nhds ht,
    (hfinite.image (Model.liftPoint E g m)).subset ?_⟩
  intro z hz
  have hnonzero : Model.liftCoefficients δ E g m k α z ≠ 0 := hz.2
  by_cases h : Model.liftPoint E g m (m.map.left z) = z
  · refine ⟨m.map.left z, ⟨hz.1, ?_⟩, h⟩
    simpa [Model.liftCoefficients, h] using hnonzero
  · simp [Model.liftCoefficients, h] at hnonzero

/-- The explicit cycle over an envelope that lifts a cycle on the target. -/
def Model.liftCycle (m : Model E V g) (k : ℤ)
    (α : CycleGroup V.left (V.hom.relativeDimensionFunction δ) k) :
    CycleGroup m.Y.left
      (@Scheme.Hom.relativeDimensionFunction _ _ m.Y.hom m.finiteType δ) k := by
  classical
  refine ⟨{ toFun := Model.liftCoefficients δ E g m k α
            supportWithinDomain' := Set.subset_univ _
            supportLocallyFiniteWithinDomain' :=
              fun y _ => Model.liftCoefficients_locallyFinite δ E g m k α y }, ?_⟩
  apply (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mpr
  intro y hy
  change Model.liftCoefficients δ E g m k α y ≠ 0 at hy
  by_cases h : Model.liftPoint E g m (m.map.left y) = y
  · have ha : α.1 (m.map.left y) ≠ 0 := by
      simpa [Model.liftCoefficients, h] using hy
    calc
      _ = V.hom.relativeDimensionFunction δ (m.map.left y) := by
        simpa only [h] using Model.liftPoint_dimension δ E g m (m.map.left y)
      _ = k := (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mp α.2 _ ha
  · simp [Model.liftCoefficients, h] at hy

/-- A Chow representative is lifted as a cycle on the base-changed input model,
then included into that model's summand of the fixed cover. `Quotient.out` uses
the proved quotient representative theorem, not `chowClass_surjective`. -/
def coverPreimage (k : ℤ) (β : RelativeChow δ V k) :
    ⨁ m : Model E V g, ModelChow δ E g k m := by
  classical
  let m := Model.ofDefined E g defined
  letI := m.finiteType
  exact DirectSum.of (ModelChow δ E g k) m
    (@chowClass m.Y.left (LocallyOfFiniteType.isLocallyNoetherian m.Y.hom)
      (@Scheme.Hom.relativeDimensionFunction _ _ m.Y.hom m.finiteType δ)
      inferInstance k (Model.liftCycle δ E g m k (Quotient.out β)))

/-- The explicit lift pushes forward to the original Chow class. -/
theorem coverPreimage_rightInverse (k : ℤ) :
    Function.RightInverse (coverPreimage δ E g defined k) (coverMap δ E g k) := sorry

include perfect defined in
/-- Envelopes remain envelopes under base change. The fixed family includes
every base-changed model, so its actual pushforward-sum map is surjective. -/
theorem coverMap_surjective (k : ℤ) : Function.Surjective (coverMap δ E g k) := by
  intro β
  exact ⟨coverPreimage δ E g defined k β, coverPreimage_rightInverse δ E g defined k β⟩

include perfect defined in
/-- Common envelope refinements and equality of complex Chern classes for
derived-isomorphic finite-free models make the specified sum operation kill
the kernel of the displayed pushforward sum. -/
theorem beforeDescent_kills_kernel (rankBound : Bool) (q : ℕ) (k : ℤ) :
    (coverMap δ E g k).ker ≤
      (beforeDescent (δ := δ) (classes := classes) (E := E) (g := g)
        rankBound q k).ker := sorry

/-- The degree-`q` operation on relative Chow groups obtained by descending the
model-wise Chern operations through the envelope pushforward map. -/
def operation (rankBound : Bool) (q : ℕ) (k : ℤ) :
    RelativeChow δ V k →+ RelativeChow δ V (k - (q : ℤ)) :=
  (coverMap δ E g k).liftOfRightInverse (coverPreimage δ E g defined k)
    (coverPreimage_rightInverse δ E g defined k)
    ⟨beforeDescent (δ := δ) (classes := classes) (E := E) (g := g) rankBound q k,
      beforeDescent_kills_kernel (δ := δ) (classes := classes) (E := E) (g := g)
        perfect defined rankBound q k⟩

/-- The descended operation agrees with the model-wise operation after the envelope
pushforward map. -/
theorem operation_cover (rankBound : Bool) (q : ℕ) (k : ℤ)
    (z : ⨁ m : Model E V g, ModelChow δ E g k m) :
    operation (δ := δ) (classes := classes) (E := E) (g := g)
        perfect defined rankBound q k (coverMap δ E g k z) =
      beforeDescent (δ := δ) (classes := classes) (E := E) (g := g)
        rankBound q k z :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

variable {V' : Over S} [LocallyOfFiniteType V'.hom]
  (a : V' ⟶ X) (j : V' ⟶ V) [LocallyOfFiniteType g.left]
  (square : IsPullback a.left j.left (𝟙 X.left) g.left)

/-- The descended Chern operation transported across an identity base-change square. -/
def capAt (rankBound : Bool) (q : ℕ) (k : ℤ) :
    RelativeChow δ V k →+ RelativeChow δ V' (k - (q : ℤ)) := by
  -- Local instance justification (defeq pin): the square proves the forgotten map is an isomorphism.
  letI : IsIso ((Over.forget S).map j) := square.isIso_snd_of_isIso
  -- Local instance justification (proof-local temporary data): `Over.forget` reflects that isomorphism.
  letI : IsIso j := isIso_of_reflects_iso j (Over.forget S)
  -- Local instance justification (defeq pin): expose the underlying-scheme inverse isomorphism.
  letI : IsIso (inv j).left := inferInstanceAs (IsIso ((Over.forget S).map (inv j)))
  -- Local instance justification (proof-local temporary data): an isomorphism is proper for this pushforward.
  letI : IsProper (inv j).left := by infer_instance
  exact (ChowGroup.map δ V V' (inv j) (k - (q : ℤ))).comp
    (operation (δ := δ) (classes := classes) (E := E) (g := g)
      perfect defined rankBound q k)

/-- The cartesian-square-indexed cap family of the descended derived Chern operation. -/
def capFamily (rankBound : Bool) (q : ℕ) : BivariantClass.CapFamily δ (𝟙 X) (q : ℤ) :=
  fun {_ _} _ _ a j g _ square k =>
    capAt (δ := δ) (classes := classes) (E := E) (g := g)
      (a := a) (j := j) (square := square) perfect defined rankBound q k

/-- The descended cap family commutes with proper pushforward. -/
theorem cap_proper (rankBound : Bool) (q : ℕ) :
    BivariantClass.CompatibleWithProperPushforward δ
      (capFamily (δ := δ) (classes := classes) (E := E)
        perfect defined rankBound q) := sorry

/-- The descended cap family commutes with flat pullback. -/
theorem cap_flat (rankBound : Bool) (q : ℕ) :
    BivariantClass.CompatibleWithFlatPullback δ
      (capFamily (δ := δ) (classes := classes) (E := E)
        perfect defined rankBound q) := sorry

/-- The descended cap family commutes with effective-Cartier Gysin pullback. -/
theorem cap_gysin (rankBound : Bool) (q : ℕ) :
    BivariantClass.CompatibleWithCartierGysin δ
      (capFamily (δ := δ) (classes := classes) (E := E)
        perfect defined rankBound q) := sorry

/-- The derived Newton class (`rankBound = false`) or total Chern class
(`rankBound = true`) obtained by envelope descent. -/
def derivedClass (rankBound : Bool) (q : ℕ) : BivariantClass δ (𝟙 X) (q : ℤ) where
  cap := capFamily (δ := δ) (classes := classes) (E := E) perfect defined rankBound q
  map_proper := cap_proper (δ := δ) (classes := classes) (E := E)
    perfect defined rankBound q
  pullback_flat := cap_flat (δ := δ) (classes := classes) (E := E)
    perfect defined rankBound q
  gysin_cartier := cap_gysin (δ := δ) (classes := classes) (E := E)
    perfect defined rankBound q

end AlgebraicGeometry.LocalizedChern.EnvelopeCaps
