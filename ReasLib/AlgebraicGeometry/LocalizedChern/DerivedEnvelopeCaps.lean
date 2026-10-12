/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
models is used only in the surjectivity law, never to choose a model.
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

include perfect defined in
/-- Envelopes remain envelopes under base change. The fixed family includes
every base-changed model, so its actual pushforward-sum map is surjective. -/
theorem coverMap_surjective (k : ℤ) : Function.Surjective (coverMap δ E g k) := by
  sorry

include perfect defined in
/-- Common envelope refinements and equality of complex Chern classes for
derived-isomorphic finite-free models make the specified sum operation kill
the kernel of the displayed pushforward sum. -/
theorem beforeDescent_kills_kernel (rankBound : Bool) (q : ℕ) (k : ℤ) :
    (coverMap δ E g k).ker ≤
      (beforeDescent (δ := δ) (classes := classes) (E := E) (g := g)
        rankBound q k).ker := by
  sorry

/-- The degree-`q` operation on relative Chow groups obtained by descending the
model-wise Chern operations through the envelope pushforward map. -/
def operation (rankBound : Bool) (q : ℕ) (k : ℤ) :
    RelativeChow δ V k →+ RelativeChow δ V (k - (q : ℤ)) :=
  (coverMap δ E g k).liftOfSurjective (coverMap_surjective δ E g perfect defined k)
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
        perfect defined rankBound q) := by sorry

/-- The descended cap family commutes with flat pullback. -/
theorem cap_flat (rankBound : Bool) (q : ℕ) :
    BivariantClass.CompatibleWithFlatPullback δ
      (capFamily (δ := δ) (classes := classes) (E := E)
        perfect defined rankBound q) := by sorry

/-- The descended cap family commutes with effective-Cartier Gysin pullback. -/
theorem cap_gysin (rankBound : Bool) (q : ℕ) :
    BivariantClass.CompatibleWithCartierGysin δ
      (capFamily (δ := δ) (classes := classes) (E := E)
        perfect defined rankBound q) := by sorry

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
