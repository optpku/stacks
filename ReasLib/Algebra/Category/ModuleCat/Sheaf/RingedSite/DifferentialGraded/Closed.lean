module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.IntClosed
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Colimit
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed cochain complexes of module sheaves on a ringed site

This file registers the ringed-site specialization of the generic cochain internal Hom. It also
exposes the canonical right-oriented internal-Hom owner used by balanced tensor products of
differential graded bimodules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Cochain

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The canonical closed structure on integer cochain complexes of module sheaves. -/
@[stacks 0FRS "closed cochain complexes on a ringed site", instance_reducible]
noncomputable instance monoidalClosed :
    MonoidalClosed (CochainComplex (ringedSiteModuleCategory J O) ℤ) :=
  CategoryTheory.CochainComplex.InternalHom.monoidalClosed

/-- The canonical right internal Hom on cochain complexes of module sheaves. -/
@[stacks 0FRS "right internal Hom for cochain complexes"]
noncomputable def rightInternalHom :
    RightInternalHom (CochainComplex (ringedSiteModuleCategory J O) ℤ) :=
  RightInternalHom.ofBraidedClosed

#synth MonoidalClosed
  (CochainComplex (ringedSiteModuleCategory J O) ℤ)
#synth BraidedCategory
  (CochainComplex (ringedSiteModuleCategory J O) ℤ)
#synth HasEqualizers
  (CochainComplex (ringedSiteModuleCategory J O) ℤ)
#synth HasCoequalizers
  (CochainComplex (ringedSiteModuleCategory J O) ℤ)
#synth ∀ X : CochainComplex (ringedSiteModuleCategory J O) ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)
#synth ∀ X : CochainComplex (ringedSiteModuleCategory J O) ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)

end SheafOfModules.RingedSite.Cochain

end
