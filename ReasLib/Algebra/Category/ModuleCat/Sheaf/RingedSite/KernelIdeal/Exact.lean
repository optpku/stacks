module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0B8S

# The additive exact sequence of a kernel ideal

A locally surjective morphism of sheaves of commutative rings has an underlying short exact
sequence of additive sheaves.  This site-level leaf owns that sequence independently of any
cohomology theory or square-zero hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

namespace KernelIdeal

variable {A Q : Sheaf J CommRingCat.{w}} (π : A ⟶ Q)

/-- The kernel ideal of `π`, viewed as an additive sheaf. -/
abbrev underlyingAdditive : Sheaf J AddCommGrpCat.{w} :=
  (SheafOfModules.toSheaf (ringSheaf J A)).obj (sheaf π)

/-- The unit `A`-module viewed as an additive sheaf. -/
abbrev underlyingUnit (A : Sheaf J CommRingCat.{w}) : Sheaf J AddCommGrpCat.{w} :=
  (SheafOfModules.toSheaf (ringSheaf J A)).obj (unitModule J A)

/-- The target term of the kernel sequence after restricting scalars to `A` and forgetting the
module structure. -/
abbrev underlyingTarget : Sheaf J AddCommGrpCat.{w} :=
  (SheafOfModules.toSheaf (ringSheaf J A)).obj
    ((SheafOfModules.pushforward (ringedSiteStructureMap π)).obj (unitModule J Q))

/-- The inclusion of the kernel ideal after forgetting to additive sheaves. -/
abbrev underlyingInclusion :
    underlyingAdditive π ⟶ underlyingUnit A :=
  (SheafOfModules.toSheaf (ringSheaf J A)).map (ι π)

/-- The underlying additive map of a morphism of commutative-ring sheaves. -/
abbrev underlyingProjection :
    underlyingUnit A ⟶ underlyingTarget π :=
  (SheafOfModules.toSheaf (ringSheaf J A)).map (map π)

/-- The underlying kernel inclusion is killed by the underlying projection. -/
@[reassoc, stacks 0B8S "underlying square-zero extension complex"]
theorem underlyingInclusion_comp_underlyingProjection :
    underlyingInclusion π ≫ underlyingProjection π = 0 := sorry

/-- The canonical underlying additive short complex `Ker π ⟶ A ⟶ Q`. -/
@[stacks 01UP "underlying additive kernel sequence",
  stacks 0B8S "underlying additive square-zero extension sequence"]
abbrev underlyingShortComplex : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (underlyingInclusion π) (underlyingProjection π)
    (underlyingInclusion_comp_underlyingProjection π)

/-- A locally surjective morphism of ring sheaves gives a short exact underlying additive
sequence. -/
@[stacks 01UP "exact underlying kernel sequence",
  stacks 0B8S "exact underlying square-zero extension sequence"]
theorem underlyingShortComplex_shortExact [Sheaf.IsLocallySurjective π] :
    (underlyingShortComplex π).ShortExact := sorry

end KernelIdeal

end SheafOfModules.RingedSite
