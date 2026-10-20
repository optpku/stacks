module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology presheaves of derived pushforwards on ringed spaces

The canonical presheaf is obtained by restricting the ringed-site cohomology presheaf along the
opens-site morphism.  Its comparison with open hypercohomology is explicit: these two models are
canonically isomorphic, but are not treated as definitionally equal.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.Cohomology

variable {X Y : RingedSpace.{u}}

/-- The presheaf on `Y` whose value over `V` is the degree-`q` cohomology of `K` over the inverse
image of `V`, modeled by restriction of the opens-ringed-site cohomology presheaf. -/
@[stacks 0D5X "preimage cohomology presheaf"]
abbrev preimagePresheaf (f : X ⟶ Y) (K : ModuleDerived X) (q : ℤ) :
    (Opens Y.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (opensRingedSiteHom f).base.op ⋙
    RingedSite.Hom.ModuleDerived.cohomologyPresheaf X.opensRingedSite K q

/-- The objectwise cohomology presheaf of the derived pushforward. -/
@[stacks 0D5X "derived-pushforward cohomology presheaf"]
abbrev pushforwardPresheaf (f : X ⟶ Y) (K : ModuleDerived X) (q : ℤ) :
    (Opens Y.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  RingedSite.Hom.ModuleDerived.cohomologyPresheaf Y.opensRingedSite
    ((moduleDerivedPushforward f).obj K) q

/-- Restricting the cohomology presheaf of `K` along `f` gives the cohomology presheaf of its
derived pushforward. -/
@[stacks 0D5X "preimage and pushforward cohomology presheaves"]
theorem preimagePresheaf_isomorphic_pushforward (f : X ⟶ Y) (K : ModuleDerived X) (q : ℤ) :
    IsIsomorphic (preimagePresheaf f K q) (pushforwardPresheaf f K q) := sorry

/-- Stacks 0D5X: sheafifying the preimage cohomology presheaf gives the underlying additive
cohomology sheaf of the derived pushforward. -/
@[stacks 0D5X "sheafification of preimage cohomology"]
theorem sheafification_isomorphic_pushforwardCohomology
    (f : X ⟶ Y) (K : ModuleDerived X) (q : ℤ) :
    IsIsomorphic
      ((presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).obj
        (preimagePresheaf f K q))
      (RingedSite.Hom.ModuleDerived.underlyingCohomologySheaf Y.opensRingedSite
        ((moduleDerivedPushforward f).obj K) q) := sorry

/-- Evaluation of the preimage cohomology presheaf over `V` agrees with hypercohomology over the
inverse-image open, after forgetting its natural section-ring module structure. -/
@[stacks 0D5X "preimage cohomology over an open"]
theorem preimagePresheaf_obj_isomorphic_openHypercohomology
    (f : X ⟶ Y) (K : ModuleDerived X) (q : ℤ) (V : Opens Y.carrier) :
    IsIsomorphic ((preimagePresheaf f K q).obj (op V))
      (moduleOpenHypercohomology X (preimageOpen f V) K q) := sorry

/-- Evaluation of the derived-pushforward cohomology presheaf over `V` agrees with
hypercohomology over its inverse image. -/
@[stacks 0D5X "pushforward cohomology over an open"]
theorem pushforwardPresheaf_obj_isomorphic_openHypercohomology
    (f : X ⟶ Y) (K : ModuleDerived X) (q : ℤ) (V : Opens Y.carrier) :
    IsIsomorphic ((pushforwardPresheaf f K q).obj (op V))
      (moduleOpenHypercohomology X (preimageOpen f V) K q) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.Cohomology

end
