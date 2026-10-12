/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Bounded.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Local
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherence from local upper bounds

This leaf packages the two local bounded-above criteria for pseudo-coherence.  The hypotheses own
the API, so the complex or derived object and the coherence index are inferred downstream.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace CochainComplex.IsLocallyBoundedAbove

/-- A locally bounded-above complex whose term in degree `i` is
`(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
@[stacks 09V7]
theorem isMPseudoCoherent
    {K : _root_.CochainComplex (Modules X) ℤ} {m : ℤ}
    (hK : CochainComplex.IsLocallyBoundedAbove K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherent (m - i)) :
    AlgebraicGeometry.RingedSpace.CochainComplex.IsMPseudoCoherent K m := sorry

end CochainComplex.IsLocallyBoundedAbove

namespace ModuleDerived.IsLocallyBoundedAbove

/-- A locally bounded-above derived module whose cohomology in degree `i` is
`(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
@[stacks 09V8]
theorem isMPseudoCoherent
    {E : ModuleDerived X} {m : ℤ}
    (hE : E.IsLocallyBoundedAbove)
    (hH : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Modules X) i).obj E).IsMPseudoCoherent (m - i)) :
    E.IsMPseudoCoherent m := sorry

end ModuleDerived.IsLocallyBoundedAbove

namespace ModuleDerived

/-- The globally bounded-above specialization of the cohomological pseudo-coherence criterion. -/
@[stacks 09V8 "bounded-above specialization"]
theorem isMPseudoCoherent_of_isLE
    {E : ModuleDerived X} {m n : ℤ}
    (hE : _root_.DerivedCategory.IsLE E n)
    (hH : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Modules X) i).obj E).IsMPseudoCoherent (m - i)) :
    E.IsMPseudoCoherent m := sorry

end ModuleDerived

end AlgebraicGeometry.RingedSpace
