module

public import ReasLib.Topology.Opens.Instances
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Generators
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.UpperResolution.Generators
import Mathlib.Tactic.CrossRefAttribute

/-!
# Upper-truncation resolutions by localized generators

The opens-site localized-generator property is the source-facing object property.  The two
statements below only specialize the generic upper-resolution and colimit owners to a ringed
space, leaving the tower itself as explicit data.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex.UpperTruncation

variable {X : RingedSpace.{u}}

/-- Lemma 20.26.11 (079T), comparison clause: a localized-generator upper-resolution tower has a
quasi-isomorphic colimit comparison. -/
@[stacks 079T "upper-resolution colimit comparison"]
theorem fromColimit_quasiIso
    {K : CochainComplex (Modules X) ℤ}
    (T : CochainComplex.UpperTruncation.Resolution
      (localizedGeneratorCoproducts X) K) :
    QuasiIso T.fromColimit := sorry

/-- Lemma 20.26.11 (079T): every complex of `𝒪_X`-modules admits a localized-generator
upper-resolution tower whose colimit comparison is a quasi-isomorphism. -/
@[stacks 079T "localized-generator upper-resolution existence"]
theorem exists_localizedGeneratorResolution
    (𝒢 : CochainComplex (Modules X) ℤ) :
    ∃ T : CochainComplex.UpperTruncation.Resolution
        (localizedGeneratorCoproducts X) 𝒢,
      QuasiIso T.fromColimit := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex.UpperTruncation

end
