module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat module sheaves and Tor on a commutative ringed site

This leaf owns the ringed-site specialization of the criterion detecting flatness by vanishing
of first Tor.  The result is stated for the two-variable K-flat Tor owner and does not ask the
module-sheaf category to have projective resolutions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived.Tor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})
variable [KFlat.HomotopyTensorDescends O] [Tensor.Has O]

/-- Lemma 21.17.15 (08FG): a module sheaf is flat exactly when its first Tor with every module
sheaf vanishes. -/
@[stacks 08FG]
theorem isFlat_iff_isZero_tor_one
    (F : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) :
    SheafOfModules.RingedSite.IsFlat O F ↔
      ∀ G : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O),
        IsZero (ModuleDerived.tor O 1 F G) := sorry

/-- A flat module sheaf has vanishing first Tor with every module sheaf. -/
@[stacks 08FG "flat modules have vanishing first Tor"]
theorem isZero_tor_one_of_isFlat
    (F : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))
    (hF : SheafOfModules.RingedSite.IsFlat O F)
    (G : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) :
    IsZero (ModuleDerived.tor O 1 F G) := sorry

/-- Vanishing of first Tor against every module sheaf detects flatness. -/
@[stacks 08FG "first Tor detects flatness"]
theorem isFlat_of_isZero_tor_one
    (F : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))
    (hTor : ∀ G : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O),
      IsZero (ModuleDerived.tor O 1 F G)) :
    SheafOfModules.RingedSite.IsFlat O F := sorry

end RingedSite.Hom.ModuleDerived.Tor

end
