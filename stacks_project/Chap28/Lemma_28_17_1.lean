/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GlobalSections.BasicOpen
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/- Lemma 28.17.1 (1): on a quasi-compact and quasi-separated scheme, restriction of global
functions to the principal open `X.basicOpen f` is localization away from `f`. -/
@[stacks 01P7] #check
  (AlgebraicGeometry.isLocalization_basicOpen_of_qcqs (X := X) (U := ⊤)
      CompactSpace.isCompact_univ isQuasiSeparated_univ :
    ∀ f : Γ(X, ⊤), IsLocalization.Away f Γ(X, X.basicOpen f))

namespace Modules

/- Lemma 28.17.1 (2): on a quasi-compact and quasi-separated scheme, restriction of a
quasi-coherent module to `X.basicOpen f` is localization away from `f`. -/
@[stacks 01P7]
#check
  (AlgebraicGeometry.Scheme.Modules.globalSections_isLocalizedModule_basicOpen :
    ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)),
      IsLocalizedModule (Submonoid.powers f)
        (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))

end Modules

end AlgebraicGeometry.Scheme
