/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.Strata

/-!
# Chow groups graded by codimension

This file defines codimension-graded Chow classes on a scheme equipped with a clopen
stratification by generic relative dimension, together with its codimension-zero fundamental
class.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- The codimension-`p` Chow group associated to generic relative-dimension strata. -/
abbrev Codimension {X S : Scheme.{u}} {f : X ⟶ S}
    [UniversallyCatenary S] [LocallyOfFiniteType f] {δ : S → ℤ} [IsDimensionFunction δ]
    (D : f.GenericDimensionStratification δ) (p : ℤ) : Type u :=
  (n : ℤ) →
    @ChowGroup (D.stratum n).toScheme
      (LocallyOfFiniteType.isLocallyNoetherian ((D.stratum n).ι ≫ f))
      (((D.stratum n).ι ≫ f).relativeDimensionFunction δ) inferInstance (n - p)

namespace Codimension

/-- The codimension-zero fundamental Chow class, componentwise given by the fundamental
cycle of each generic relative-dimension stratum. -/
noncomputable def fundamentalClass {X S : Scheme.{u}} {f : X ⟶ S}
    [UniversallyCatenary S] [LocallyOfFiniteType f] {δ : S → ℤ} [IsDimensionFunction δ]
    (D : f.GenericDimensionStratification δ) : Codimension D 0 :=
  fun n ↦
    @chowClass (D.stratum n).toScheme
      (LocallyOfFiniteType.isLocallyNoetherian ((D.stratum n).ι ≫ f))
      (((D.stratum n).ι ≫ f).relativeDimensionFunction δ) inferInstance (n - 0)
      (@CycleGroup.fundamental (D.stratum n).toScheme
        (LocallyOfFiniteType.isLocallyNoetherian ((D.stratum n).ι ≫ f))
        (((D.stratum n).ι ≫ f).relativeDimensionFunction δ) (n - 0))

/-- The `n`-th component of the fundamental class is the Chow class of the degree-`n`
fundamental cycle of the `n`-th stratum. -/
theorem fundamentalClass_apply {X S : Scheme.{u}} {f : X ⟶ S}
    [UniversallyCatenary S] [LocallyOfFiniteType f] {δ : S → ℤ} [IsDimensionFunction δ]
    (D : f.GenericDimensionStratification δ) (n : ℤ) :
    fundamentalClass D n =
      @chowClass (D.stratum n).toScheme
        (LocallyOfFiniteType.isLocallyNoetherian ((D.stratum n).ι ≫ f))
        (((D.stratum n).ι ≫ f).relativeDimensionFunction δ) inferInstance (n - 0)
        (@CycleGroup.fundamental (D.stratum n).toScheme
          (LocallyOfFiniteType.isLocallyNoetherian ((D.stratum n).ι ≫ f))
          (((D.stratum n).ι ≫ f).relativeDimensionFunction δ) (n - 0)) := sorry

end Codimension
end AlgebraicGeometry.ChowGroup
