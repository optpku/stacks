/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-injective complexes on localized ringed sites

Restriction to the localization of a ringed site is the right adjoint of exact extension by zero,
so its termwise action preserves K-injective cochain complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u v w z

namespace RingedSite.Hom

variable (X : RingedSite.{u, v, w}) (U : X) [UnivLE.{max u v, z}]
variable [SheafOfModules.Localization.HasLowerShriek.{z} X.structureSheaf]

/-- Lemma 21.20.1 (08FI): restriction to a localized ringed site preserves K-injective
cochain complexes. -/
@[stacks 08FI "localized restriction preserves K-injectives", instance]
theorem localizedRestrictionComplex_isKInjective
    (I : CochainComplex (ModuleCat.{z} X) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((localizedRestrictionComplex.{z} X U).obj I) := sorry

end RingedSite.Hom
