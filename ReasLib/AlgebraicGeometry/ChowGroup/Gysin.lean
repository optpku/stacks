/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Noetherian

/-!
# Gysin homomorphisms for zero schemes

This file defines the Gysin homomorphism associated to the zero scheme of a section of an
invertible module, together with its generator formulas and effective-Cartier intersection.
-/

@[expose] public section

open CategoryTheory Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
  (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)

/-- The reduced closure of a point is locally of finite type over the fixed base. -/
instance pointClosureToBaseLocallyOfFiniteType (x : X) :
    LocallyOfFiniteType (Scheme.PointClosure.ι x ≫ p) := sorry

/-- The zero scheme of a section is locally of finite type over the fixed base. -/
instance zeroSchemeToBaseLocallyOfFiniteType :
    LocallyOfFiniteType (zeroSchemeι ℒ s ≫ p) := sorry

/-- The canonical over-object of the zero scheme is locally of finite type over its base. -/
instance zeroSchemeOverLocallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (zeroSchemeι ℒ s ≫ p)).hom := sorry

/-- The canonical over-object of `p` retains its locally finite-type structure. -/
instance sourceOverLocallyOfFiniteType : LocallyOfFiniteType (Over.mk p).hom := sorry

/-- The zero-scheme morphism between its canonical over-objects is proper. -/
instance zeroSchemeOverHomIsProper :
    IsProper ((Over.homMk (zeroSchemeι ℒ s) :
      Over.mk (zeroSchemeι ℒ s ≫ p) ⟶ Over.mk p).left) := sorry

/-- The ideal sheaf cutting out the scheme-theoretic intersection of `Z(s)` with the
reduced closure of `x`. -/
noncomputable def zeroPointIntersection (x : X) : X.IdealSheafData :=
  zeroIdealSheaf ℒ s ⊔ (Scheme.PointClosure.reducedStructure x).ideal

/-- The point intersection is cut out by the sum of the zero-scheme ideal and the reduced
point-closure ideal. -/
theorem zeroPointIntersection_def (x : X) :
    zeroPointIntersection ℒ s x =
      zeroIdealSheaf ℒ s ⊔ (Scheme.PointClosure.reducedStructure x).ideal := sorry

/-- The canonical closed immersion from `Z(s) ∩ closure({x})` to `Z(s)`. -/
noncomputable def zeroPointIntersectionToZeroScheme (x : X) :
    (zeroPointIntersection ℒ s x).subscheme ⟶ zeroScheme ℒ s :=
  Scheme.IdealSheafData.inclusion
    (le_sup_left : zeroIdealSheaf ℒ s ≤ zeroPointIntersection ℒ s x)

/-- The intersection inclusion followed by the zero-scheme immersion is the ambient
closed-subscheme immersion. -/
theorem zeroPointIntersectionToZeroScheme_comp (x : X) :
    zeroPointIntersectionToZeroScheme ℒ s x ≫ zeroSchemeι ℒ s =
      (zeroPointIntersection ℒ s x).subschemeι := sorry

/-- The canonical map from the point intersection to the zero scheme is a closed immersion. -/
instance zeroPointIntersectionToZeroScheme_isClosedImmersion (x : X) :
    IsClosedImmersion (zeroPointIntersectionToZeroScheme ℒ s x) := sorry

/-- Containment of `x` in `Z(s)` makes the zero-scheme ideal vanish on the reduced closure
of `x`. -/
theorem zeroIdealSheaf_le_pointClosureKer (x : X)
    (hx : x ∈ (zeroIdealSheaf ℒ s).support) :
    zeroIdealSheaf ℒ s ≤ (Scheme.PointClosure.ι x).ker := sorry

/-- The canonical morphism from the reduced closure of a point contained in `Z(s)` to
the zero scheme. -/
noncomputable def pointClosureToZeroScheme (x : X)
    (hx : x ∈ (zeroIdealSheaf ℒ s).support) :
    Scheme.PointClosure.scheme x ⟶ zeroScheme ℒ s :=
  (zeroIdealSheaf ℒ s).lift (Scheme.PointClosure.ι x)
    (zeroIdealSheaf_le_pointClosureKer ℒ s x hx)

/-- The point-closure map to `Z(s)` factors its canonical immersion into `X`. -/
theorem pointClosureToZeroScheme_comp (x : X)
    (hx : x ∈ (zeroIdealSheaf ℒ s).support) :
    pointClosureToZeroScheme ℒ s x hx ≫ zeroSchemeι ℒ s =
      Scheme.PointClosure.ι x := sorry

/-- The induced map from a contained reduced point closure to the zero scheme is a closed
immersion. -/
instance pointClosureToZeroScheme_isClosedImmersion (x : X)
    (hx : x ∈ (zeroIdealSheaf ℒ s).support) :
    IsClosedImmersion (pointClosureToZeroScheme ℒ s x hx) := sorry

/-- The fundamental cycle of a reduced point closure is supported in its prescribed relative
degree. -/
theorem pointClosureFundamental_mem (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1) :
    @AlgebraicCycle.fundamental (Scheme.PointClosure.scheme x)
        (@Scheme.PointClosure.scheme_isLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) x)
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) (k + 1) ∈
      AlgebraicCycle.dimensionSubgroup
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) (k + 1) := sorry

/-- The degree-`k + 1` fundamental cycle of the reduced closure of `x`. -/
noncomputable def pointClosureFundamentalCycle (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1) :
    CycleGroup (Scheme.PointClosure.scheme x)
      ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) (k + 1) :=
  ⟨@AlgebraicCycle.fundamental (Scheme.PointClosure.scheme x)
      (@Scheme.PointClosure.scheme_isLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p) x)
      ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) (k + 1),
    pointClosureFundamental_mem p δ k x hx⟩

/-- Forgetting the grading of the point-closure fundamental cycle recovers the fundamental
algebraic cycle. -/
theorem pointClosureFundamentalCycle_toAlgebraicCycle (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1) :
    CycleGroup.toAlgebraicCycle
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) (k + 1)
        (pointClosureFundamentalCycle p δ k x hx) =
      @AlgebraicCycle.fundamental (Scheme.PointClosure.scheme x)
        (@Scheme.PointClosure.scheme_isLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) x)
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) (k + 1) := sorry

/-- The degree-`k` fundamental cycle of the scheme-theoretic intersection of `Z(s)` with
the reduced closure of `x` is supported in degree `k`. -/
theorem zeroPointIntersectionFundamental_mem (k : ℤ) (x : X) :
    @AlgebraicCycle.fundamental (zeroPointIntersection ℒ s x).subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) (zeroPointIntersection ℒ s x))
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ) k ∈
      AlgebraicCycle.dimensionSubgroup
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ) k := sorry

/-- The degree-`k` fundamental cycle of `Z(s) ∩ closure({x})`. -/
noncomputable def zeroPointIntersectionFundamentalCycle (k : ℤ) (x : X) :
    CycleGroup (zeroPointIntersection ℒ s x).subscheme
      (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ) k :=
  ⟨@AlgebraicCycle.fundamental (zeroPointIntersection ℒ s x).subscheme
      (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
        (LocallyOfFiniteType.isLocallyNoetherian p) (zeroPointIntersection ℒ s x))
      (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ) k,
    zeroPointIntersectionFundamental_mem p δ ℒ s k x⟩

/-- Forgetting the grading of the intersection fundamental cycle recovers its underlying
fundamental algebraic cycle. -/
theorem zeroPointIntersectionFundamentalCycle_toAlgebraicCycle (k : ℤ) (x : X) :
    CycleGroup.toAlgebraicCycle
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x) =
      @AlgebraicCycle.fundamental (zeroPointIntersection ℒ s x).subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) (zeroPointIntersection ℒ s x))
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ) k := sorry

/-- The cycle on `Z(s)` contributed by a degree-`k + 1` point of `X`, using the intersection
cycle off `Z(s)` and the restricted first-Chern cycle on `Z(s)`. -/
noncomputable def gysinGeneratorCycle (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1) :
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k :=
  @dite _ (x ∈ (zeroIdealSheaf ℒ s).support) (Classical.propDecidable _)
    (fun hmem ↦
      CycleGroup.mapHom (pointClosureToZeroScheme ℒ s x hmem)
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (@firstChernCycle (Scheme.PointClosure.scheme x)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) x)
          ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) inferInstance
          ((pullback (Scheme.PointClosure.ι x)).obj ℒ) inferInstance k
          (pointClosureFundamentalCycle p δ k x hx)))
    (fun _ ↦
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x))

/-- Off `Z(s)`, the Gysin generator is the pushed-forward degree-`k` fundamental cycle of
the scheme-theoretic intersection with the reduced point closure. -/
theorem gysinGeneratorCycle_of_not_mem (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroIdealSheaf ℒ s).support) :
    gysinGeneratorCycle p δ ℒ s k x hx =
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x) := sorry

/-- On `Z(s)`, the Gysin generator is the pushforward of first-Chern intersection with the
fundamental cycle of the reduced point closure. -/
theorem gysinGeneratorCycle_of_mem (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroIdealSheaf ℒ s).support) :
    gysinGeneratorCycle p δ ℒ s k x hx =
      CycleGroup.mapHom (pointClosureToZeroScheme ℒ s x hmem)
        ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (@firstChernCycle (Scheme.PointClosure.scheme x)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) x)
          ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) inferInstance
          ((pullback (Scheme.PointClosure.ι x)).obj ℒ) inferInstance k
          (pointClosureFundamentalCycle p δ k x hx)) := sorry

/-- The coefficient-weighted Gysin generator cycles of a degree-`k + 1` cycle form a locally
finite family on `Z(s)`. -/
theorem gysinGeneratorTermsLocallyFinite (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    LocallyFinite fun x : X ↦
      (CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (if hx : p.relativeDimensionFunction δ x = k + 1 then
          (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
            gysinGeneratorCycle p δ ℒ s k x hx
        else 0)).support := sorry

/-- The explicit locally finite cycle on `Z(s)` obtained by extending the two generator rules
linearly. -/
noncomputable def gysinCycle (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k :=
  CycleGroup.locallyFiniteSum
    ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
    (fun x : X ↦
      if hx : p.relativeDimensionFunction δ x = k + 1 then
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
          gysinGeneratorCycle p δ ℒ s k x hx
      else 0)
    (gysinGeneratorTermsLocallyFinite p δ ℒ s k α)

/-- Coefficients of the Gysin cycle are the pointwise finite sums of the weighted generator
cycles. -/
theorem gysinCycle_apply (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1))
    (z : zeroScheme ℒ s) :
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (gysinCycle p δ ℒ s k α) z =
      ∑ᶠ x : X,
        CycleGroup.toAlgebraicCycle
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (if hx : p.relativeDimensionFunction δ x = k + 1 then
            (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
              gysinGeneratorCycle p δ ℒ s k x hx
          else 0) z := sorry

/-- Taking the Chow class of the Gysin cycle sends zero to zero. -/
theorem gysinCycleClass_zero (k : ℤ) :
    @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (gysinCycle p δ ℒ s k 0) = 0 := sorry

/-- Taking the Chow class of the Gysin cycle preserves addition. -/
theorem gysinCycleClass_add (k : ℤ)
    (α β : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (gysinCycle p δ ℒ s k (α + β)) =
      @chowClass (zeroScheme ℒ s)
          (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
            ℒ inferInstance s)
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
          (gysinCycle p δ ℒ s k α) +
        @chowClass (zeroScheme ℒ s)
          (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
            ℒ inferInstance s)
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
          (gysinCycle p δ ℒ s k β) := sorry

/-- The Gysin homomorphism from degree-`k + 1` cycles on `X` to degree-`k` Chow classes
on the zero scheme `Z(s)`. -/
noncomputable def gysin (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
      @ChowGroup (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k where
  toFun := fun α ↦ @chowClass (zeroScheme ℒ s)
    (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
      ℒ inferInstance s)
    ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
    (gysinCycle p δ ℒ s k α)
  map_zero' := gysinCycleClass_zero p δ ℒ s k
  map_add' := gysinCycleClass_add p δ ℒ s k

/-- The Gysin homomorphism is computed by the explicit locally finite Gysin cycle followed by
passage to the Chow quotient. -/
theorem gysin_apply (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    gysin p δ ℒ s k α =
      @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (gysinCycle p δ ℒ s k α) := sorry

/-- On a generator not contained in `Z(s)`, the Gysin homomorphism is the Chow class of the
scheme-theoretic intersection `Z(s) ∩ closure({x})`. -/
theorem gysin_point_of_not_mem (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroIdealSheaf ℒ s).support) :
    gysin p δ ℒ s k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) =
      @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
          (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (zeroPointIntersectionFundamentalCycle p δ ℒ s k x)) := sorry

/-- On a generator contained in `Z(s)`, the Gysin homomorphism is the pushforward of
`c₁(ℒ|closure({x})) ∩ [closure({x})]`. -/
theorem gysin_point_of_mem (k : ℤ) (x : X)
    (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroIdealSheaf ℒ s).support) :
    gysin p δ ℒ s k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) =
      @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (CycleGroup.mapHom (pointClosureToZeroScheme ℒ s x hmem)
          ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ)
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (@firstChernCycle (Scheme.PointClosure.scheme x)
            (@Scheme.PointClosure.scheme_isLocallyNoetherian X
              (LocallyOfFiniteType.isLocallyNoetherian p) x)
            ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) inferInstance
            ((pullback (Scheme.PointClosure.ι x)).obj ℒ) inferInstance k
            (pointClosureFundamentalCycle p δ k x hx))) := sorry

/-- Intersection with the effective Cartier divisor `Z(s)`, obtained by proper pushforward
of the Gysin class along `Z(s) ⟶ X`. -/
noncomputable def cartierIntersection [IsEffectiveCartierDivisor (zeroSchemeι ℒ s)] (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k :=
  (ChowGroup.map δ (Over.mk (zeroSchemeι ℒ s ≫ p)) (Over.mk p)
      (Over.homMk (zeroSchemeι ℒ s)) k).comp (gysin p δ ℒ s k)

/-- Effective-Cartier intersection is the proper pushforward of the Gysin class along the
zero-scheme immersion. -/
theorem cartierIntersection_apply [IsEffectiveCartierDivisor (zeroSchemeι ℒ s)] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    cartierIntersection p δ ℒ s k α =
      ChowGroup.map δ (Over.mk (zeroSchemeι ℒ s ≫ p)) (Over.mk p)
        (Over.homMk (zeroSchemeι ℒ s)) k (gysin p δ ℒ s k α) := sorry

end AlgebraicGeometry.Scheme.Modules
