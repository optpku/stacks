module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.Local
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dualizable locally strictly perfect complexes

For the canonical total tensor product on cochain complexes of `𝒪_X`-modules, local strict
perfectness is exactly dualizability.  This leaf is independent of any chosen internal Hom.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- Example 20.50.2: a locally strictly perfect complex of `𝒪_X`-modules is right-dualizable
for the canonical total tensor product.  This is the Mathlib orientation of the source's
left-dual convention. -/
@[stacks 0FP9 "locally strictly perfect implies dualizable"]
theorem IsLocallyStrictlyPerfect.isRightDualizable
    {F : _root_.CochainComplex (Modules X) ℤ}
    (hF : IsLocallyStrictlyPerfect F) :
    IsRightDualizable F := sorry

/-- Lemma 20.50.3: a right-dualizable complex of `𝒪_X`-modules is locally strictly perfect. -/
@[stacks 0FPA "dualizable implies locally strictly perfect"]
theorem isLocallyStrictlyPerfect_of_isRightDualizable
    {F : _root_.CochainComplex (Modules X) ℤ}
    (hF : IsRightDualizable F) :
    IsLocallyStrictlyPerfect F := sorry

/-- Lemma 20.50.3: explicit source-order exact-pairing data make the first complex locally
strictly perfect. -/
@[stacks 0FPA "explicit exact-pairing form"]
theorem IsLocallyStrictlyPerfect.ofExactPairing
    {F G : _root_.CochainComplex (Modules X) ℤ} (p : ExactPairing F G) :
    IsLocallyStrictlyPerfect F := sorry

/-- Local strict perfectness is exactly right dualizability for the canonical total tensor
product on complexes of `𝒪_X`-modules. -/
@[stacks 0FP9 "forward implication", stacks 0FPA "reverse implication"]
theorem isLocallyStrictlyPerfect_iff_isRightDualizable
    (F : _root_.CochainComplex (Modules X) ℤ) :
    IsLocallyStrictlyPerfect F ↔ IsRightDualizable F := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
