module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module

/-!
# Small-étale restriction of étale modules

Compatibility check for the canonical associated étale module restriction functor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.GroupoidsOver.restrictModulesToSmallEtale :
  ∀ (X : GroupoidsOver S) (x : X.total),
    etaleModules X ⥤
      RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite (X.p.obj x).left))
