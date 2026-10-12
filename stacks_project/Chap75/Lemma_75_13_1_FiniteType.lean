/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheafification

/-!
# Finite type along the small étale-to-Zariski restriction

Finite type of an `𝒪_X`-module on the small Zariski ringed site is equivalent to
finite type of its inverse image along `smallEtaleToZariski`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- Inverse image along `smallEtaleToZariski` preserves finite type of module sheaves. -/
instance smallEtaleToZariski_modulePullback_isFiniteType {X : Scheme.{u}}
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite X))
    [F.IsFiniteType] :
    ((smallEtaleToZariski X).modulePullback.obj F).IsFiniteType := sorry

/-- Finite type of the inverse image along `smallEtaleToZariski` implies finite type of
the original `𝒪_X`-module. -/
theorem smallEtaleToZariski_isFiniteType_of_modulePullback {X : Scheme.{u}}
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite X)) :
    ((smallEtaleToZariski X).modulePullback.obj F).IsFiniteType → F.IsFiniteType :=
  sorry

/-- Finite type of an `𝒪_X`-module on the small Zariski site is equivalent to finite type
of its inverse image along `smallEtaleToZariski` on the small étale site. -/
theorem smallEtaleToZariski_isFiniteType_iff {X : Scheme.{u}}
    (F : RingedSite.ModuleCat.{u} (Scheme.Zariski.Small.ringedSite X)) :
    F.IsFiniteType ↔
      ((smallEtaleToZariski X).modulePullback.obj F).IsFiniteType := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
