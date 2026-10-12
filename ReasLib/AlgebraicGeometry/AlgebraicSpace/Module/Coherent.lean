/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeRestriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.Topology.Sheaves.Abelian.Over

@[expose] public section

open CategoryTheory
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A module on an algebraic space is coherent when its restriction to every small étale
scheme chart is a coherent Zariski module. -/
class IsCoherent (F : Modules X) : Prop where
  /-- Restriction to each étale scheme chart is coherent. -/
  coherentOnChart (chart : site X) : SheafOfModules.IsCoherent ((toScheme chart).obj F)

/-- Coherence of a small étale module is equivalent to coherence on all scheme charts. -/
theorem isCoherent_iff (F : Modules X) :
    IsCoherent F ↔ ∀ chart : site X, SheafOfModules.IsCoherent ((toScheme chart).obj F) := sorry

/-- The zero module on an algebraic space is coherent. -/
instance isCoherentZero : IsCoherent (0 : Modules X) := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
