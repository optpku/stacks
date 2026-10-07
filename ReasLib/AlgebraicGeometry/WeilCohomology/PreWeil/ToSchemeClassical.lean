module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.Point
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.PoincareDuality
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.SchemePushforward
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.CycleClassPushforward
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.SchemeAxiomA8
public import ReasLib.AlgebraicGeometry.WeilCohomology.GradedPullback
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.IsWeil

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u v w x y z

namespace WeilCohomology.SchemePreWeilTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0} {H Picard : V → Type w}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]

variable (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
  cyclePullback cyclePushforward pointCycle H Picard)

/-- The homogeneous pieces of a presented pre-Weil theory are multiplicatively graded. -/
def gradedMonoidHgrade (X : V) : SetLike.GradedMonoid (T.Hgrade X) where
  one_mem := T.one_mem X
  mul_mem := fun {_i _j a b} ha hb ↦ T.mul_mem X ⟨a, ha⟩ ⟨b, hb⟩

/-- The exhaustive homogeneous decomposition of a presented pre-Weil theory gives its
canonical graded-algebra structure. -/
noncomputable def gradedAlgebraHgrade (X : V) : GradedAlgebra (T.Hgrade X) :=
  -- Local instance justification (proof-local temporary data): DirectSum.IsInternal.gradedAlgebra requires SetLike.GradedMonoid from gradedMonoidHgrade
  letI := T.gradedMonoidHgrade X
  DirectSum.IsInternal.gradedAlgebra (T.Hgrade_isInternal X)

/-- The pullback of a presented pre-Weil theory as a bundled graded algebra homomorphism. -/
def gradedPullback {X Y : V} (f : X ⟶ Y) :=
  -- Local instance justification (proof-local temporary data): GradedAlgHom notation needs GradedAlgebra from gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  ({ T.pullback f with
    map_mem := fun {i a} ha ↦ T.pullback_mem f i ⟨a, ha⟩ } : T.Hgrade Y →ₐᵍ[F] T.Hgrade X)

/-- The bundled graded pullback agrees with the original pullback on total cohomology. -/
theorem gradedPullback_apply {X Y : V} (f : X ⟶ Y) (a : H Y) :
    T.gradedPullback f a = T.pullback f a := sorry

/-- The morphism to the chosen point object obtained from the geometric structure map. -/
noncomputable def structureMorphism (X : V) : X ⟶ point :=
  T.scheme_fullyFaithful.preimage
    (Over.homMk (T.scheme.obj X).hom ≫ T.schemePoint.inv)

/-- The represented structure morphism is the canonical map to `Spec(k)`. -/
theorem scheme_structureMorphism (X : V) :
    T.scheme.map (T.structureMorphism X) ≫ T.schemePoint.hom =
      Over.homMk (T.scheme.obj X).hom := sorry

/-- The Künneth map is the product of the two newly bundled graded pullbacks. -/
theorem kunnethMap_tmul_gradedPullback (X Y : V) (a : H X) (b : H Y) :
    T.kunnethMap X Y (a ⊗ₜ[F] b) =
      T.gradedPullback (fst X Y) a * T.gradedPullback (snd X Y) b := sorry

/-- The underlying Chow class chosen among the pushforwards of fundamental classes of
presentations of a closed point. -/
noncomputable def closedPointClassValue {X : V}
    (p : closedPoints (T.scheme.obj X).left) : CH X :=
  Classical.epsilon fun c : CH X ↦
    ∃ (P : V)
      (e : T.scheme.obj P ≅
        Over.mk ((T.scheme.obj X).left.fromSpecResidueField p ≫ (T.scheme.obj X).hom))
      (f : P ⟶ X),
      (T.scheme.map f).left =
          e.hom.left ≫ (T.scheme.obj X).left.fromSpecResidueField p ∧
        c = cyclePushforward f
          (cyclePullback (T.structureMorphism P) (1 : CHgrade point 0))

/-- The chosen closed-point cycle has codimension equal to the dimension of its ambient
nonempty equidimensional scheme. -/
theorem closedPointClassValue_mem {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left) :
    T.closedPointClassValue p ∈ CHgrade X d := sorry

/-- The Chow class of a closed point, constructed from a chosen presented copy of its
residue-field spectrum and Chow pushforward. -/
noncomputable def closedPointClass {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left) : CHgrade X d :=
  ⟨T.closedPointClassValue p, T.closedPointClassValue_mem hX p⟩

/-- A closed-point class is represented by the pushforward of the fundamental class on a
presentation of its residue-field spectrum. -/
theorem closedPointClass_spec {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left) :
    ∃ (P : V)
      (e : T.scheme.obj P ≅
        Over.mk ((T.scheme.obj X).left.fromSpecResidueField p ≫ (T.scheme.obj X).hom))
      (f : P ⟶ X),
      (T.scheme.map f).left =
          e.hom.left ≫ (T.scheme.obj X).left.fromSpecResidueField p ∧
        (T.closedPointClass hX p : CH X) =
          cyclePushforward f
            (cyclePullback (T.structureMorphism P) (1 : CHgrade point 0)) := sorry

/-- Pushing a constructed closed-point class to the point gives its residue-field degree. -/
theorem closedPointClass_pushforward {X : V} {d : ℕ}
    (hX : T.IsNonemptyEquidimensional X d)
    (p : closedPoints (T.scheme.obj X).left)
    [FiniteDimensional k ((T.scheme.obj X).left.residueField p)] :
    cyclePushforward (T.structureMorphism X) (T.closedPointClass hX p) =
      (Module.finrank k ((T.scheme.obj X).left.residueField p) : ℤ) •
        (1 : CHgrade point 0) := sorry

/-- The explicit scheme-valued classical theory determined by data (D0), (D1), and
(D2') satisfying axioms (A1)–(A8). -/
noncomputable def toSchemeClassicalTheory
    (hA8 : T.SatisfiesAxiomA8) :=
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  id (α := SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH T.Hgrade CHgrade cyclePullback cyclePushforward) {
    scheme := T.scheme
    scheme_fullyFaithful := T.scheme_fullyFaithful
    smooth := T.smooth
    projective := T.projective
    dimension_eq := sorry
    schemeProduct := T.schemeProduct
    scheme_fst := T.scheme_fst
    scheme_snd := T.scheme_snd
    schemePoint := T.schemePoint
    structureMorphism := T.structureMorphism
    scheme_structureMorphism := T.scheme_structureMorphism
    scheme_essentiallySurjective := T.scheme_essentiallySurjective
    cyclePullback_id := T.cyclePullback_id
    cyclePullback_comp := T.cyclePullback_comp
    cyclePushforward_id := T.cyclePushforward_id
    cyclePushforward_comp := T.cyclePushforward_comp
    IsNonemptyEquidimensional := T.IsNonemptyEquidimensional
    nonemptyEquidimensional_iff := T.nonemptyEquidimensional_iff
    product_isNonemptyEquidimensional := T.product_isNonemptyEquidimensional
    point_isNonemptyEquidimensional := T.point_isNonemptyEquidimensional
    fundamentalClass_pullback := sorry
    closedPointClass := T.closedPointClass
    closedPointClass_pushforward := T.closedPointClass_pushforward
    tateLine_rank := T.tateLine_rank
    Hgrade_isInternal := T.Hgrade_isInternal
    tateTwist := T.tateTwist
    pullback := T.gradedPullback
    pullback_id := sorry
    pullback_comp := sorry
    gradedComm := T.gradedComm
    cycleClass := T.cycleClass
    cycleClass_mem := T.cycleClass_mem
    integral := T.integral
    integral_vanishes := T.integral_vanishes
    finiteDimensional := T.finiteDimensional_of_axiomsA1ToA7
    poincarePairing := T.poincarePairing
    poincarePairing_apply := T.poincarePairing_apply
    poincarePairing_bijective := T.poincarePairing_bijective_of_axiomsA1ToA7
    pushforward := T.pushforward
    pushforward_mem := sorry
    pushforward_spec := sorry
    kunnethMap := T.kunnethMap
    kunnethMap_tmul := T.kunnethMap_tmul_gradedPullback
    kunnethMap_mem := fun _X _Y _p _q a b ↦ T.kunnethMap_mem a b
    kunnethMap_bijective := kunnethMap_bijective_of_axiomsA1ToA7 T
    integral_kunnethMap_tmul := fun {X Y : V} {d e : ℕ} hX hY a b ↦
      integral_kunnethMap_tmul_of_axiomsA1ToA7 T X Y hX hY a b
    cyclePushforward_mem := sorry
    cycleClass_pullback := T.cycleClass_pullback
    cycleClass_pushforward := cycleClass_pushforward_of_axiomsA1ToA8 T hA8
    cycleClass_mul := T.cycleClass_mul
    point_normalization := T.point_normalization }

/-- The conversion retains the geometric realization functor. -/
theorem toSchemeClassicalTheory_scheme (hA8 : T.SatisfiesAxiomA8) :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).scheme = T.scheme := sorry

/-- The conversion retains the cycle-class homomorphism. -/
theorem toSchemeClassicalTheory_cycleClass (hA8 : T.SatisfiesAxiomA8) (X : V) :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).cycleClass X = T.cycleClass X := sorry

/-- The conversion retains the geometric nonempty-equidimensional predicate. -/
theorem toSchemeClassicalTheory_isNonemptyEquidimensional
    (hA8 : T.SatisfiesAxiomA8) {X : V} {d : ℕ} :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).IsNonemptyEquidimensional X d ↔
      T.IsNonemptyEquidimensional X d := sorry

/-- The conversion retains the zero-extended trace. -/
theorem toSchemeClassicalTheory_integral (hA8 : T.SatisfiesAxiomA8)
    {X : V} {d : ℕ} (hX : T.IsNonemptyEquidimensional X d) :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).integral
        ((T.toSchemeClassicalTheory_isNonemptyEquidimensional hA8).mpr hX) =
      T.integral hX := sorry

/-- The conversion retains the Poincaré-duality pushforward. -/
theorem toSchemeClassicalTheory_pushforward (hA8 : T.SatisfiesAxiomA8)
    {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
    (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).pushforward
        ((T.toSchemeClassicalTheory_isNonemptyEquidimensional hA8).mpr hX)
        ((T.toSchemeClassicalTheory_isNonemptyEquidimensional hA8).mpr hY) f =
      T.pushforward hX hY f := sorry

/-- The conversion retains the Künneth map. -/
theorem toSchemeClassicalTheory_kunnethMap (hA8 : T.SatisfiesAxiomA8) (X Y : V) :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).kunnethMap X Y = T.kunnethMap X Y := sorry

/-- Degree-zero pullback in the converted theory is the original restricted pullback. -/
theorem toSchemeClassicalTheory_degreeZeroPullback (hA8 : T.SatisfiesAxiomA8)
    {X Y : V} (f : X ⟶ Y) (a : T.Hgrade Y (0, 0)) :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).degreeZeroPullback f a =
      T.pullbackGrade f (0, 0) a := sorry

/-- Data (D0), (D1), and (D2') satisfying axioms (A1)–(A8) determine a scheme-valued
Weil cohomology theory. -/
theorem isWeil_of_axiomsA1ToA8 (hA8 : T.SatisfiesAxiomA8) :
  -- Local instance justification (proof-local temporary data): SchemeClassicalTheory takes GradedAlgebra as a typeclass binder, while the graded algebra on T.Hgrade is constructed by gradedAlgebraHgrade
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.gradedAlgebraHgrade
  (T.toSchemeClassicalTheory hA8).IsWeil := sorry

end WeilCohomology.SchemePreWeilTheory
