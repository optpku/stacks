module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Divided powers on ideal sheaves

This leaf owns divided-power structures on ideal sheaves over arbitrary
ringed sites.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v w

/-- A divided-power structure on an ideal sheaf assigns divided powers to every
section ideal and makes them commute with restriction maps. -/
structure DividedPowerIdealSheaf
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (O : Sheaf J CommRingCat.{w})
    (I : Subobject (unitModule J O)) where
  /-- The divided powers on the ideal of sections over each object of the site. -/
  dividedPowers : ∀ U : Cᵒᵖ,
    DividedPowers (IdealSheaf.sections I U)
  /-- The sectionwise divided powers commute with restriction maps on ideal sections. -/
  natural :
    ∀ (n : ℕ+) {U V : Cᵒᵖ} (f : U ⟶ V)
      (x : IdealSheaf.sections I U),
      O.obj.map f ((dividedPowers U).dpow n x) =
        (dividedPowers V).dpow n (O.obj.map f x)

namespace DividedPowerIdealSheaf

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}}
variable {I : Subobject (unitModule J O)}

/-- Construct a divided-power ideal sheaf from objectwise divided powers and their
restriction compatibility. -/
def of
    (dpow : ∀ U : Cᵒᵖ,
      DividedPowers (IdealSheaf.sections I U))
    (natural :
      ∀ (n : ℕ+) {U V : Cᵒᵖ} (f : U ⟶ V)
        (x : IdealSheaf.sections I U),
        O.obj.map f ((dpow U).dpow n x) =
          (dpow V).dpow n (O.obj.map f x)) :
    DividedPowerIdealSheaf J O I :=
  { dividedPowers := dpow
    natural := natural }

/-- The ambient divided-power operation on sections over an object `U`. -/
def dpow (γ : DividedPowerIdealSheaf J O I) (n : ℕ) (U : Cᵒᵖ) :
    O.obj.obj U → O.obj.obj U :=
  (γ.dividedPowers U).dpow n

/-- The positive divided-power operation on the ideal of sections over `U`. -/
def dpowOnSections (γ : DividedPowerIdealSheaf J O I) (n : ℕ+) (U : Cᵒᵖ) :
    IdealSheaf.sections I U → IdealSheaf.sections I U :=
  fun x ↦
    ⟨γ.dpow n U x,
      (γ.dividedPowers U).dpow_mem n.ne_zero x.property⟩

/-- The operation `dpow` agrees with the divided-power structure on each section ideal. -/
lemma dpow_apply (γ : DividedPowerIdealSheaf J O I) (n : ℕ) (U : Cᵒᵖ)
    (x : O.obj.obj U) :
    γ.dpow n U x = (γ.dividedPowers U).dpow n x := sorry

/-- Coercing `dpowOnSections` to the ambient ring recovers the ambient operation. -/
lemma dpowOnSections_apply (γ : DividedPowerIdealSheaf J O I) (n : ℕ+) (U : Cᵒᵖ)
    (x : IdealSheaf.sections I U) :
    (γ.dpowOnSections n U x : O.obj.obj U) = γ.dpow n U x := sorry

/-- Restriction maps preserve the divided-power operations on sections of the ideal sheaf. -/
lemma map_dpow (γ : DividedPowerIdealSheaf J O I) (n : ℕ+)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : IdealSheaf.sections I U) :
    O.obj.map f (γ.dpow n U x) = γ.dpow n V (O.obj.map f x) := sorry

end DividedPowerIdealSheaf
