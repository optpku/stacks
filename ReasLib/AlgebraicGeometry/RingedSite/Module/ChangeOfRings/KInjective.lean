/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-Injectivity Under Coextension of Scalars

Same-site restriction of scalars is exact.  Its canonical right adjoint, coextension of scalars,
therefore preserves K-injective cochain complexes.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.coextendAlong

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O O' : Sheaf J CommRingCat.{max u v}}

/-- Lemma 21.20.11 (093Z): coextension of scalars along a morphism of ring sheaves preserves
K-injective cochain complexes. -/
@[stacks 093Z "coextension of scalars preserves K-injectives", instance]
theorem mapComplex_isKInjective (alpha : O ⟶ O')
    (I : CochainComplex (ringedSiteModuleCategory J O) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((coextendAlong alpha).mapHomologicalComplex (up ℤ)).obj I) := sorry

end SheafOfModules.RingedSite.coextendAlong
