module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin

/-!
# Cycle-level Gysin maps for trivial restrictions

This file defines the cycle-valued Gysin map associated to a section of an invertible
module whose pullback to its zero scheme is trivial, together with its generator formulas
and compatibility with Chow classes.
-/

@[expose] public section

open CategoryTheory Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
  (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)

/-- The cycle contributed by a degree-`k + 1` point when the restriction of `ℒ` to
`Z(s)` is trivial: it is zero on `Z(s)` and the scheme-theoretic intersection cycle
away from `Z(s)`. -/
noncomputable def trivialGysinGeneratorCycle
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1) :
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k :=
  @dite _ (x ∈ (zeroIdealSheaf ℒ s).support) (Classical.propDecidable _)
    (fun _ ↦ 0)
    (fun _ ↦
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x))

/-- A generator supported on `Z(s)` contributes zero to the trivial-restriction Gysin
cycle. -/
theorem trivialGysinGeneratorCycle_of_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroIdealSheaf ℒ s).support) :
    trivialGysinGeneratorCycle p δ ℒ s htriv k x hx = 0 := sorry

/-- A generator away from `Z(s)` contributes the pushed-forward fundamental cycle of
its scheme-theoretic intersection with `Z(s)`. -/
theorem trivialGysinGeneratorCycle_of_not_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroIdealSheaf ℒ s).support) :
    trivialGysinGeneratorCycle p δ ℒ s htriv k x hx =
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x) := sorry

/-- The coefficient-weighted trivial-restriction Gysin generator cycles form a locally
finite family on `Z(s)`. -/
theorem trivialGysinGeneratorTermsLocallyFinite
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    LocallyFinite fun x : X ↦
      (CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (if hx : p.relativeDimensionFunction δ x = k + 1 then
          (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
            trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
        else 0)).support := sorry

/-- The explicit cycle obtained by extending the trivial-restriction generator rule
linearly. -/
noncomputable def trivialGysinCycle
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k :=
  CycleGroup.locallyFiniteSum
    ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
    (fun x : X ↦
      if hx : p.relativeDimensionFunction δ x = k + 1 then
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
          trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
      else 0)
    (trivialGysinGeneratorTermsLocallyFinite p δ ℒ s htriv k α)

/-- Coefficients of the trivial-restriction Gysin cycle are the pointwise finite sums of
the weighted generator cycles. -/
theorem trivialGysinCycle_apply
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1))
    (z : zeroScheme ℒ s) :
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (trivialGysinCycle p δ ℒ s htriv k α) z =
      ∑ᶠ x : X,
        CycleGroup.toAlgebraicCycle
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (if hx : p.relativeDimensionFunction δ x = k + 1 then
            (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
              trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
          else 0) z := sorry

/-- The concrete trivial-restriction Gysin cycle sends zero to zero. -/
theorem trivialGysinCycle_zero
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ)) (k : ℤ) :
    trivialGysinCycle p δ ℒ s htriv k 0 = 0 := sorry

/-- The concrete trivial-restriction Gysin cycle preserves addition. -/
theorem trivialGysinCycle_add
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α β : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    trivialGysinCycle p δ ℒ s htriv k (α + β) =
      trivialGysinCycle p δ ℒ s htriv k α + trivialGysinCycle p δ ℒ s htriv k β := sorry

/-- The canonical additive cycle map associated to a section whose line bundle becomes
trivial on its zero scheme. -/
noncomputable def trivialGysin
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ)) (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
      CycleGroup (zeroScheme ℒ s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k where
  toFun := trivialGysinCycle p δ ℒ s htriv k
  map_zero' := trivialGysinCycle_zero p δ ℒ s htriv k
  map_add' := trivialGysinCycle_add p δ ℒ s htriv k

/-- On a point generator contained in `Z(s)`, the trivial-restriction Gysin map is zero. -/
theorem trivialGysin_point_of_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroIdealSheaf ℒ s).support) :
    trivialGysin p δ ℒ s htriv k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) = 0 := sorry

/-- On a point generator away from `Z(s)`, the trivial-restriction Gysin map is the
pushed-forward scheme-theoretic intersection cycle. -/
theorem trivialGysin_point_of_not_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroIdealSheaf ℒ s).support) :
    trivialGysin p δ ℒ s htriv k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) =
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x) := sorry

/-- Passage to Chow classes identifies the trivial-restriction cycle map with the Gysin
homomorphism. -/
theorem trivialGysin_chowClass
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (trivialGysin p δ ℒ s htriv k α) =
      gysin p δ ℒ s k α := sorry

end AlgebraicGeometry.Scheme.Modules
