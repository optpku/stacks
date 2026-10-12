/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClass

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

namespace AlgebraicGeometry.ChowGroup

namespace ChernCap

/-- The pushforward to `X` of the degree-`k - j` component of the total Chern class
of the pullback of `E` to an integral closed subscheme `W`. -/
noncomputable def integralValue.{u}
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    {W : Over S} [LocallyOfFiniteType W.hom] [IsIntegral W.left]
    (i : W ⟶ X) [IsClosedImmersion i.left] (k : ℤ)
    (hk : W.hom.relativeDimensionFunction δ (genericPoint W.left) = k)
    (j : Fin (r + 1)) {P : Scheme.{u}} (π : P ⟶ W.left)
    (hπ : Scheme.ProjectiveBundle.Representation π
      ((Scheme.Modules.pullback i.left).obj E))
    [LocallyOfFiniteType (π ≫ W.hom)]
    (F : ProjectiveBundleFormula δ W.hom
      ((Scheme.Modules.pullback i.left).obj E) r π hπ k hk)
    (hF : F.IsGeometric δ W.hom ((Scheme.Modules.pullback i.left).obj E)
      r π hπ k hk) :
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ)) :=
  ChowGroup.map δ W X i (k - (j : ℕ))
    (ProjectiveBundleFormula.totalChernClass δ W.hom
      ((Scheme.Modules.pullback i.left).obj E) r π hπ k hk F hF (k - (j : ℕ)))

universe v

/-- `integralValue` is the proper pushforward of the indicated homogeneous component
of the total Chern class on `W`. -/
theorem integralValue_def
    {S : Scheme.{v}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    {W : Over S} [LocallyOfFiniteType W.hom] [IsIntegral W.left]
    (i : W ⟶ X) [IsClosedImmersion i.left] (k : ℤ)
    (hk : W.hom.relativeDimensionFunction δ (genericPoint W.left) = k)
    (j : Fin (r + 1)) {P : Scheme.{v}} (π : P ⟶ W.left)
    (hπ : Scheme.ProjectiveBundle.Representation π
      ((Scheme.Modules.pullback i.left).obj E))
    [LocallyOfFiniteType (π ≫ W.hom)]
    (F : ProjectiveBundleFormula δ W.hom
      ((Scheme.Modules.pullback i.left).obj E) r π hπ k hk)
    (hF : F.IsGeometric δ W.hom ((Scheme.Modules.pullback i.left).obj E)
      r π hπ k hk) :
    integralValue δ E r i k hk j π hπ F hF =
      ChowGroup.map δ W X i (k - (j : ℕ))
        (ProjectiveBundleFormula.totalChernClass δ W.hom
          ((Scheme.Modules.pullback i.left).obj E) r π hπ k hk F hF
          (k - (j : ℕ))) := sorry

/-- Explicit projective-bundle data used to evaluate Definition 42.37.1 on the
reduced closure of a point of dimension `k`. -/
structure IntegralFormula.{u}
    {S : Scheme.{u}} [hS : UniversallyCatenary S] (δ : S → ℤ) [hδ : IsDimensionFunction δ]
    (X : Over S) [hX : LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (x : X.left) where
  /-- The reduced point closure is locally of finite type over `S`. -/
  pointClosureLocallyOfFiniteType :
    LocallyOfFiniteType (Scheme.PointClosure.ι x ≫ X.hom)
  /-- The generic point of the reduced point closure has dimension `k`. -/
  dimension :
    (Scheme.PointClosure.ι x ≫ X.hom).relativeDimensionFunction δ
      (genericPoint (Scheme.PointClosure.scheme x)) = k
  /-- A projective bundle on the reduced point closure. -/
  P : Scheme.{u}
  /-- The projective-bundle morphism. -/
  π : P ⟶ Scheme.PointClosure.scheme x
  /-- The projective bundle represents invertible quotients of the pulled-back module. -/
  representation : Scheme.ProjectiveBundle.Representation π
    ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E)
  /-- The projective bundle is locally of finite type over `S`. -/
  projectiveBundleLocallyOfFiniteType :
    LocallyOfFiniteType (π ≫ Scheme.PointClosure.ι x ≫ X.hom)
  /-- The projective-bundle formula used to compute the Chern classes. -/
  formula :
    @ProjectiveBundleFormula S (Scheme.PointClosure.scheme x) P δ
      (Scheme.PointClosure.ι x ≫ X.hom) hS hδ pointClosureLocallyOfFiniteType
      (Scheme.PointClosure.scheme_isIntegral x)
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E) r
      (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank (Scheme.PointClosure.scheme x)
        X.left (Scheme.PointClosure.ι x) E r hE)
      π representation projectiveBundleLocallyOfFiniteType k dimension
  /-- The formula is the geometric projective-bundle formula of Definition 42.37.1. -/
  geometric :
    @ProjectiveBundleFormula.IsGeometric S (Scheme.PointClosure.scheme x) P δ
      (Scheme.PointClosure.ι x ≫ X.hom) hS hδ pointClosureLocallyOfFiniteType
      (Scheme.PointClosure.scheme_isIntegral x)
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E) r
      (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank (Scheme.PointClosure.scheme x)
        X.left (Scheme.PointClosure.ι x) E r hE)
      π representation projectiveBundleLocallyOfFiniteType k dimension formula

namespace IntegralFormula

/-- Build the formula data at a point from a specified geometric projective bundle. -/
def ofFormula.{u}
    {S : Scheme.{u}} [hS : UniversallyCatenary S] (δ : S → ℤ) [hδ : IsDimensionFunction δ]
    (X : Over S) [hX : LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (x : X.left)
    (hfinite : LocallyOfFiniteType (Scheme.PointClosure.ι x ≫ X.hom))
    (hk : (Scheme.PointClosure.ι x ≫ X.hom).relativeDimensionFunction δ
      (genericPoint (Scheme.PointClosure.scheme x)) = k)
    {P : Scheme.{u}} (π : P ⟶ Scheme.PointClosure.scheme x)
    (hπ : Scheme.ProjectiveBundle.Representation π
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E))
    (hP : LocallyOfFiniteType (π ≫ Scheme.PointClosure.ι x ≫ X.hom))
    (F : @ProjectiveBundleFormula S (Scheme.PointClosure.scheme x) P δ
      (Scheme.PointClosure.ι x ≫ X.hom) hS hδ hfinite
      (Scheme.PointClosure.scheme_isIntegral x)
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E) r
      (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank (Scheme.PointClosure.scheme x)
        X.left (Scheme.PointClosure.ι x) E r hE)
      π hπ hP k hk)
    (hF : @ProjectiveBundleFormula.IsGeometric S (Scheme.PointClosure.scheme x) P δ
      (Scheme.PointClosure.ι x ≫ X.hom) hS hδ hfinite
      (Scheme.PointClosure.scheme_isIntegral x)
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E) r
      (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank (Scheme.PointClosure.scheme x)
        X.left (Scheme.PointClosure.ι x) E r hE)
      π hπ hP k hk F) :
    IntegralFormula δ X E r k x where
  pointClosureLocallyOfFiniteType := hfinite
  dimension := hk
  P := P
  π := π
  representation := hπ
  projectiveBundleLocallyOfFiniteType := hP
  formula := F
  geometric := hF

end IntegralFormula

end ChernCap

/-- A family of additive Chern-class intersection operations on cycles, normalized in
degree zero and characterized on integral closed subschemes. -/
structure ChernCap.{u}
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] where
  /-- Intersection with `c_j(E)` on cycles of degree `k`. -/
  cap : ∀ (k : ℤ) (j : Fin (r + 1)),
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) k →+
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))
  /-- Intersection with `c_0(E)` is passage from cycles to their Chow classes. -/
  capZero : ∀ k : ℤ,
    cap k 0 =
      (@reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm).toAddMonoidHom.comp
          (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) inferInstance k)
  /-- On the fundamental cycle of an integral closed subscheme, the cap is the
  pushforward of the Chern class of the restricted module. -/
  capIntegral :
    ∀ {W : Over S} [LocallyOfFiniteType W.hom] [IsIntegral W.left]
      (i : W ⟶ X) [IsClosedImmersion i.left] (k : ℤ)
      (hk : W.hom.relativeDimensionFunction δ (genericPoint W.left) = k)
      (j : Fin (r + 1)) {P : Scheme.{u}} (π : P ⟶ W.left)
      (hπ : Scheme.ProjectiveBundle.Representation π
        ((Scheme.Modules.pullback i.left).obj E))
      [LocallyOfFiniteType (π ≫ W.hom)]
      (F : ProjectiveBundleFormula δ W.hom
        ((Scheme.Modules.pullback i.left).obj E) r π hπ k hk)
      (hF : F.IsGeometric δ W.hom ((Scheme.Modules.pullback i.left).obj E)
        r π hπ k hk),
      cap k j
          (CycleGroup.mapHom i.left (W.hom.relativeDimensionFunction δ)
            (X.hom.relativeDimensionFunction δ) k
            (@CycleGroup.fundamental W.left
              (LocallyOfFiniteType.isLocallyNoetherian W.hom)
              (W.hom.relativeDimensionFunction δ) k)) =
        ChernCap.integralValue δ E r i k hk j π hπ F hF

namespace ChernCap

universe u

/-- The degree-`k - j` Chow class on a reduced point closure supplied by an
explicit instance of Definition 42.37.1. -/
noncomputable def IntegralFormula.chernClass
    {S : Scheme.{u}} [hS : UniversallyCatenary S] (δ : S → ℤ) [hδ : IsDimensionFunction δ]
    (X : Over S) [hX : LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (x : X.left)
    (F : IntegralFormula δ X E r k x) (j : Fin (r + 1)) :
    @ChowGroup (Scheme.PointClosure.scheme x)
      (@Scheme.PointClosure.scheme_isLocallyNoetherian X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom) x)
      ((Scheme.PointClosure.ι x ≫ X.hom).relativeDimensionFunction δ)
      (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction
        (Scheme.PointClosure.scheme x) S (Scheme.PointClosure.ι x ≫ X.hom)
        hS F.pointClosureLocallyOfFiniteType δ hδ) (k - (j : ℕ)) :=
  @ProjectiveBundleFormula.totalChernClass S (Scheme.PointClosure.scheme x) F.P δ
    (Scheme.PointClosure.ι x ≫ X.hom) hS hδ F.pointClosureLocallyOfFiniteType
    (Scheme.PointClosure.scheme_isIntegral x)
    ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E) r
    (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank (Scheme.PointClosure.scheme x)
      X.left (Scheme.PointClosure.ι x) E r hE)
    F.π F.representation F.projectiveBundleLocallyOfFiniteType k F.dimension
    F.formula F.geometric (k - (j : ℕ))

/-- `IntegralFormula.chernClass` is the indicated homogeneous component of the
total Chern class from Definition 42.37.1. -/
theorem IntegralFormula.chernClass_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (x : X.left)
    (F : IntegralFormula δ X E r k x) (j : Fin (r + 1)) :
    F.chernClass δ X E r k x j =
      @ProjectiveBundleFormula.totalChernClass S (Scheme.PointClosure.scheme x) F.P δ
        (Scheme.PointClosure.ι x ≫ X.hom) inferInstance inferInstance
        F.pointClosureLocallyOfFiniteType (Scheme.PointClosure.scheme_isIntegral x)
        ((Scheme.Modules.pullback (Scheme.PointClosure.ι x)).obj E) r
        (@Scheme.Modules.pullback_isFiniteLocallyFreeOfRank (Scheme.PointClosure.scheme x)
          X.left (Scheme.PointClosure.ι x) E r inferInstance)
        F.π F.representation F.projectiveBundleLocallyOfFiniteType k F.dimension
        F.formula F.geometric (k - (j : ℕ)) := sorry

/-- A cycle representative on `X` of the pushed-forward Chern class attached to
the reduced closure of `x`. -/
noncomputable def integralCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (x : X.left)
    (F : IntegralFormula δ X E r k x) (j : Fin (r + 1)) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k - (j : ℕ)) :=
  CycleGroup.mapHom (Scheme.PointClosure.ι x)
    ((Scheme.PointClosure.ι x ≫ X.hom).relativeDimensionFunction δ)
    (X.hom.relativeDimensionFunction δ) (k - (j : ℕ))
    (Quotient.out (F.chernClass δ X E r k x j))

/-- The representative `integralCycle` is supported on the closure of its source point. -/
theorem integralCycle_support
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ) (x : X.left)
    (F : IntegralFormula δ X E r k x) (j : Fin (r + 1)) :
    (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (k - (j : ℕ))
      (integralCycle δ X E r k x F j)).support ⊆
        (Scheme.PointClosure.closedSubset x : Set X.left) := sorry

/-- The term contributed by `x` to the Chern cap of a degree-`k` cycle. -/
noncomputable def generatorTerm
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x)
    (k : ℤ) (j : Fin (r + 1))
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) (x : X.left) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k - (j : ℕ)) :=
  if hx : X.hom.relativeDimensionFunction δ x = k then
    (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) k alpha x) •
      integralCycle δ X E r k x (F k x hx) j
  else 0

/-- The generator terms selected by a cycle form a locally finite family. -/
theorem generatorTermsLocallyFinite
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x)
    (k : ℤ) (j : Fin (r + 1))
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) :
    LocallyFinite fun x : X.left ↦
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (k - (j : ℕ))
        (generatorTerm δ X E r F k j alpha x)).support := sorry

/-- The cycle representative obtained by the locally finite extension of the
Definition 42.37.1 values on integral point closures. -/
noncomputable def cycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x)
    (k : ℤ) (j : Fin (r + 1))
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k - (j : ℕ)) :=
  CycleGroup.locallyFiniteSum (X.hom.relativeDimensionFunction δ) (k - (j : ℕ))
    (generatorTerm δ X E r F k j alpha)
    (generatorTermsLocallyFinite δ X E r F k j alpha)

/-- The locally finite Chern-cycle construction sends zero to zero in the Chow group. -/
theorem cycleClass_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x) (k : ℤ) (j : Fin (r + 1)) :
    @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))
      (cycle δ X E r F k j 0) = 0 := sorry

/-- The locally finite Chern-cycle construction preserves addition in the Chow group. -/
theorem cycleClass_add
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x) (k : ℤ) (j : Fin (r + 1))
    (alpha beta : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) :
    @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))
      (cycle δ X E r F k j (alpha + beta)) =
        @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))
          (cycle δ X E r F k j alpha) +
        @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))
          (cycle δ X E r F k j beta) := sorry

/-- Intersection with the `j`th Chern class, explicitly extended from integral
point closures to all locally finite degree-`k` cycles. -/
noncomputable def operation
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x)
    (k : ℤ) (j : Fin (r + 1)) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) k →+
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ)) where
  toFun := fun alpha ↦
    @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))
      (cycle δ X E r F k j alpha)
  map_zero' := cycleClass_zero δ X E r F k j
  map_add' := cycleClass_add δ X E r F k j

/-- On every cycle, `operation` is the Chow class of the locally finite sum of
its coefficient-weighted integral-generator values. -/
theorem operation_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x)
    (k : ℤ) (j : Fin (r + 1))
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) :
    operation δ X E r F k j alpha =
      @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ))
        (CycleGroup.locallyFiniteSum (X.hom.relativeDimensionFunction δ)
          (k - (j : ℕ)) (generatorTerm δ X E r F k j alpha)
          (generatorTermsLocallyFinite δ X E r F k j alpha)) := sorry

/-- The concrete operation is independent of the geometric formula data used
to represent the integral-generator Chern classes. -/
theorem operation_eq_of_formulas
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F G : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x) (k : ℤ) (j : Fin (r + 1)) :
    operation δ X E r F k j = operation δ X E r G k j := sorry

/-- The degree-zero member of the concrete Chern-cap family is passage to Chow classes. -/
theorem operation_zeroIndex
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x) (k : ℤ) :
    operation δ X E r F k 0 =
      (@reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm).toAddMonoidHom.comp
          (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) inferInstance k) := sorry

/-- On an integral closed subscheme, the concrete operation is the pushforward
of the Chern class of the restricted module. -/
theorem operation_integral
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (G : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x)
    {W : Over S} [LocallyOfFiniteType W.hom] [IsIntegral W.left]
    (i : W ⟶ X) [IsClosedImmersion i.left] (k : ℤ)
    (hk : W.hom.relativeDimensionFunction δ (genericPoint W.left) = k)
    (j : Fin (r + 1)) {P : Scheme.{u}} (π : P ⟶ W.left)
    (hπ : Scheme.ProjectiveBundle.Representation π
      ((Scheme.Modules.pullback i.left).obj E))
    [LocallyOfFiniteType (π ≫ W.hom)]
    (F : ProjectiveBundleFormula δ W.hom
      ((Scheme.Modules.pullback i.left).obj E) r π hπ k hk)
    (hF : F.IsGeometric δ W.hom ((Scheme.Modules.pullback i.left).obj E)
      r π hπ k hk) :
    operation δ X E r G k j
        (CycleGroup.mapHom i.left (W.hom.relativeDimensionFunction δ)
          (X.hom.relativeDimensionFunction δ) k
          (@CycleGroup.fundamental W.left
            (LocallyOfFiniteType.isLocallyNoetherian W.hom)
            (W.hom.relativeDimensionFunction δ) k)) =
      integralValue δ E r i k hk j π hπ F hF := sorry

/-- Construct the characterized Chern-cap family from the explicit locally finite
extension of the integral formulas. -/
noncomputable def ofIntegralFormulas
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x) : ChernCap δ X E r where
  cap := operation δ X E r F
  capZero := operation_zeroIndex δ X E r F
  capIntegral := operation_integral δ X E r F

/-- The cap projection of `ofIntegralFormulas` is the concrete locally finite operation. -/
theorem ofIntegralFormulas_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
      IntegralFormula δ X E r k x) :
    (ofIntegralFormulas δ X E r F).cap = operation δ X E r F := sorry

/-- A Chern-cap operation satisfies both its degree-zero normalization and its formula
on the fundamental cycles of integral closed subschemes. -/
theorem spec
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (c : ChernCap δ X E r) :
    (∀ k : ℤ,
      c.cap k 0 =
        (@reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance k (k - (0 : ℕ))
          (sub_zero k).symm).toAddMonoidHom.comp
            (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction δ) inferInstance k)) ∧
      ∀ {W : Over S} [LocallyOfFiniteType W.hom] [IsIntegral W.left]
        (i : W ⟶ X) [IsClosedImmersion i.left] (k : ℤ)
        (hk : W.hom.relativeDimensionFunction δ (genericPoint W.left) = k)
        (j : Fin (r + 1)) {P : Scheme.{u}} (π : P ⟶ W.left)
        (hπ : Scheme.ProjectiveBundle.Representation π
          ((Scheme.Modules.pullback i.left).obj E))
        [LocallyOfFiniteType (π ≫ W.hom)]
        (F : ProjectiveBundleFormula δ W.hom
          ((Scheme.Modules.pullback i.left).obj E) r π hπ k hk)
        (hF : F.IsGeometric δ W.hom ((Scheme.Modules.pullback i.left).obj E)
          r π hπ k hk),
        c.cap k j
            (CycleGroup.mapHom i.left (W.hom.relativeDimensionFunction δ)
              (X.hom.relativeDimensionFunction δ) k
              (@CycleGroup.fundamental W.left
                (LocallyOfFiniteType.isLocallyNoetherian W.hom)
                (W.hom.relativeDimensionFunction δ) k)) =
          integralValue δ E r i k hk j π hπ F hF := sorry

end ChernCap

end AlgebraicGeometry.ChowGroup
