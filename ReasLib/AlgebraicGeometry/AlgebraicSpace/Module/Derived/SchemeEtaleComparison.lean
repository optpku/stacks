module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.SmallEtale
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward

/-! # Derived comparison with the small étale site of a scheme -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pushforward of modules along `schemeEtaleRingedHom U` preserves finite limits. -/
instance schemeEtaleRingedHom_modulePushforward_preservesFiniteLimits
    {S : Scheme.{u}} (U : Over S) :
    PreservesFiniteLimits (schemeEtaleRingedHom U).modulePushforward.{u} :=
  sorry

/-- Pushforward of modules along `schemeEtaleRingedHom U` preserves finite colimits. -/
instance schemeEtaleRingedHom_modulePushforward_preservesFiniteColimits
    {S : Scheme.{u}} (U : Over S) :
    PreservesFiniteColimits (schemeEtaleRingedHom U).modulePushforward.{u} :=
  sorry

namespace DerivedQCoh

/-- Pushforward along the canonical comparison of small étale ringed sites induces
a functor from derived modules on a represented algebraic space to derived modules on
the underlying scheme's small étale site. -/
def toEtaleDerived {S : Scheme.{u}} (U : Over S) :
    ModuleDerived (ofOver U) ⥤
      DerivedCategory (RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left)) :=
  (schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory

/-- `toEtaleDerived U` is exact derived pushforward along `schemeEtaleRingedHom U`. -/
theorem toEtaleDerived_eq {S : Scheme.{u}} (U : Over S) :
    toEtaleDerived U =
      (schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory :=
  rfl

/-- Objectwise, `toEtaleDerived` is exact derived pushforward along
`schemeEtaleRingedHom U`. -/
theorem toEtaleDerived_obj {S : Scheme.{u}} (U : Over S)
    (K : ModuleDerived (ofOver U)) :
    (toEtaleDerived U).obj K =
      ((schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory).obj K :=
  rfl

end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
