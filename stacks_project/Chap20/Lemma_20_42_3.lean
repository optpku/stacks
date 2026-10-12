/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.42.3 (08DL): for a ringed space `X`, an open `U`, and derived modules `K`, `L`,
restriction identifies `RHom(K, L)|_U` with `RHom(K|_U, L|_U)`.  The reusable owner is the
localized-ringed-site comparison in `RingedSite.Hom.LocalizedRestriction.InternalHom`; this file
only recalls it at the canonical opens ringed site of `X`. -/
@[stacks 08DL]
#check @RingedSite.Hom.LocalizedRestriction.InternalHom.comparison

#check @RingedSite.Hom.LocalizedRestriction.InternalHom.comparison_isIso

section

variable {X : RingedSpace.{u}} (U : TopologicalSpace.Opens X.carrier)
variable [MonoidalCategory (RingedSite.Hom.ModuleDerived.{u} (opensRingedSite X))]
variable [BraidedCategory (RingedSite.Hom.ModuleDerived.{u} (opensRingedSite X))]
variable [MonoidalClosed (RingedSite.Hom.ModuleDerived.{u} (opensRingedSite X))]
variable [MonoidalCategory
  (RingedSite.Hom.ModuleDerived.{u} ((opensRingedSite X).localization U))]
variable [BraidedCategory
  (RingedSite.Hom.ModuleDerived.{u} ((opensRingedSite X).localization U))]
variable [MonoidalClosed
  (RingedSite.Hom.ModuleDerived.{u} ((opensRingedSite X).localization U))]
variable [Functor.Monoidal
  (RingedSite.Hom.localizedRestrictionDerived.{u} (opensRingedSite X) U)]
variable (K L : RingedSite.Hom.ModuleDerived.{u} (opensRingedSite X))

/- The specialization retains the source objects and makes the direction of the comparison
explicit without introducing a chapter-local alias or instance pin. -/
#check RingedSite.Hom.LocalizedRestriction.InternalHom.comparison
  (opensRingedSite X) U K L
#check RingedSite.Hom.LocalizedRestriction.InternalHom.comparison_isIso
  (opensRingedSite X) U (K := K) (L := L)

end

end AlgebraicGeometry.RingedSpace
