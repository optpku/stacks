module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

/-!
# Semi-Free Resolutions

This leaf owns the bundled data of a quasi-isomorphic semi-free replacement
of a differential graded module.  Construction and existence results live in
the separate `SemiFree.Resolution.Existence` leaf.
-/

open CategoryTheory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

/-- A semi-free resolution of a differential graded `A`-module is a quasi-isomorphism from a
cochain complex admitting a semi-free filtration. -/
structure SemiFreeResolution (M : ModuleCat.DGMod A) where
  /-- The semi-free resolving complex. -/
  complex : ModuleCat.DGMod A
  /-- The comparison map from the resolving complex to the target. -/
  π : complex ⟶ M
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso : QuasiIso π
  /-- The resolving complex has a semi-free filtration. -/
  hasSemiFreeFiltration : HasSemiFreeFiltration complex

attribute [instance] SemiFreeResolution.quasiIso

namespace SemiFreeResolution

/-- A semi-free resolution can be used as its resolving differential graded module. -/
instance {M : ModuleCat.DGMod A} :
    CoeOut (SemiFreeResolution M) (ModuleCat.DGMod A) where
  coe P := P.complex

end SemiFreeResolution

end CochainComplex
