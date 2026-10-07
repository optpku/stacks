module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Koszul
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul complexes on commutative ringed sites

The reusable owner is stated on an arbitrary commutative ringed site.  Its presheaf differential
comes from `PresheafOfModules.Koszul`; this file performs only the canonical module
sheafification and packages the resulting maps into a chain complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Koszul

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The sectionwise Koszul chain complex before module sheafification. -/
@[stacks 062K "sectionwise Koszul chain complex"]
noncomputable abbrev presheafComplex
    {F : ringedSiteModuleCategory J O} (phi : F ⟶ unitModule J O) :
    ChainComplex (PresheafOfModules (ringSheaf J O).obj) ℕ :=
  PresheafOfModules.Koszul.complex O.obj phi.val

/-- The degree-`n + 1` sectionwise Koszul differential before module sheafification. -/
@[stacks 062K "sectionwise Koszul differential"]
noncomputable abbrev presheafDifferential
    {F : ringedSiteModuleCategory J O} (phi : F ⟶ unitModule J O) (n : ℕ) :
    ExteriorPower.presheaf O F (n + 1) ⟶ ExteriorPower.presheaf O F n :=
  PresheafOfModules.Koszul.differential O.obj phi.val n

/-- The degree-`n + 1` Koszul differential of module sheaves on a commutative ringed site. -/
@[stacks 062K "ringed-site differential"]
noncomputable def differential
    {F : ringedSiteModuleCategory J O} (phi : F ⟶ unitModule J O) (n : ℕ) :
    ExteriorPower.sheaf O F (n + 1) ⟶ ExteriorPower.sheaf O F n :=
  (moduleSheafification O).map (presheafDifferential O phi n)

/-- Consecutive sheafified Koszul differentials compose to zero.  The `reassoc` companion is the
standard chain-map interface for inserting an arbitrary morphism after the two-step composite. -/
@[reassoc, stacks 062K "square-zero law for the ringed-site differential"]
theorem differential_sq
    {F : ringedSiteModuleCategory J O} (phi : F ⟶ unitModule J O) (n : ℕ) :
    differential O phi (n + 1) ≫ differential O phi n = 0 := sorry

/-- The Koszul chain complex attached to a morphism from a module sheaf to the structure
module on a commutative ringed site. -/
@[stacks 062K]
noncomputable def complex
    {F : ringedSiteModuleCategory J O} (phi : F ⟶ unitModule J O) :
    ChainComplex (ringedSiteModuleCategory J O) ℕ :=
  ChainComplex.of (fun n ↦ ExteriorPower.sheaf O F n)
    (differential O phi) (differential_sq O phi)

/-- The degree-`n` term of a ringed-site Koszul complex is the degree-`n` exterior-power sheaf. -/
@[stacks 062K "Koszul complex term"]
theorem complex_X
    {F : ringedSiteModuleCategory J O} (phi : F ⟶ unitModule J O) (n : ℕ) :
    (complex O phi).X n = ExteriorPower.sheaf O F n := sorry

/-- The differential from degree `n + 1` to degree `n` in the ringed-site Koszul complex is the
canonical sheafified Koszul differential. -/
@[stacks 062K "Koszul complex differential"]
theorem complex_d
    {F : ringedSiteModuleCategory J O} (phi : F ⟶ unitModule J O) (n : ℕ) :
    (complex O phi).d (n + 1) n = differential O phi n := sorry

end SheafOfModules.RingedSite.Koszul
