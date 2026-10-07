module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.23.4

The reusable owner states the fixed-base resolution theorem directly in the category of right DG
modules.  Degreewise surjectivity is represented by `Epi π.toCochainMap`, while surjectivity on
cycles is the generic complex-map predicate `π.toCochainMap.EpiOnCycles`.  This entry does not
claim that the chosen source remains good after arbitrary ringed-topos base change.
-/

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}
variable (M : Mod(A, d))

/- Lemma 24.23.4 (0FSE), fixed-base form: every right DG module has a fixed-base-good cover
which is epimorphic degreewise and on cycles. -/
@[stacks 0FSE "fixed-base-good cover"]
#check
  (IsGoodAtBase.exists_cover M :
    ∃ (P : Mod(A, d)) (π : P ⟶ M),
      Epi π.toCochainMap ∧ π.toCochainMap.EpiOnCycles ∧ IsGoodAtBase P)

/- Fine-grained cycle-map API used to consume the cover one degree at a time. -/
variable {P Q : Mod(A, d)} (f : P ⟶ Q) (n : ℤ)

#check
  (HomologicalComplex.cyclesMap f.toCochainMap n :
    P.toComplex.cycles n ⟶ Q.toComplex.cycles n)
#check (f.toCochainMap.EpiOnCycles : Prop)
#check
  (HomologicalComplex.Hom.epiOnCycles_iff f.toCochainMap :
    f.toCochainMap.EpiOnCycles ↔
      ∀ i, Epi (HomologicalComplex.cyclesMap f.toCochainMap i))
#check
  (HomologicalComplex.epi_iff_epi_f f.toCochainMap :
    Epi f.toCochainMap ↔ ∀ i, Epi (f.toCochainMap.f i))

variable (hf : f.toCochainMap.EpiOnCycles)

#check
  (hf.epi n : Epi (HomologicalComplex.cyclesMap f.toCochainMap n))

end SheafOfModules.RingedSite.DifferentialGradedModule

end
