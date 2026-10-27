/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.CechSpectralSequence
import StacksCheckRecall

/-!
# Cohomology of a quasi-coherent module via an fppf Čech nerve

A surjective flat 1-morphism of algebraic stacks that is representable by
algebraic spaces and locally of finite presentation computes fppf cohomology
of a quasi-coherent module from the relative Čech nerve.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Proposition 103.11.6: A representable, surjective, flat morphism of algebraic
stacks locally of finite presentation gives a Čech spectral sequence for a
quasi-coherent module. The pinned proposition displays
`E₂^{p, q} = H^q(𝒰_p, f_p^* F) ⇒ H^{p+q}(𝒳, F)`, but its proof cites
Proposition 96.20.1, whose fppf formula displays `E₁^{p, q}`. This check uses
the cited theorem's standard Čech indexing: simplex cohomology is page 1,
with differential degree `(r, 1-r)`. Here `𝒰_p` has `p + 1` factors over `𝒳`
and `f_p` is `Cech.proj f ⦋p⦌`. -/
@[stacks 0784] #check (AlgebraicGeometry.GroupoidsOver.exists_qcohRelativeCechSpectralSequence :
    ∀ {S : Scheme.{u}} {U X : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X)
    (F : SheafOfModules.{u} (associatedStructureSheaf X StandardTopology.fppf))
    [F.IsQuasicoherent] [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [HasSheafify (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.fppf p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1}
      (Sheaf (relativeCechSite f StandardTopology.fppf p) AddCommGrpCat.{u + 1})],
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechModulePageOne f StandardTopology.fppf
            (RingedSite.Module.carrierLift (associatedRingedSite X StandardTopology.fppf) F) p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology StandardTopology.fppf) n).obj
          ((SheafOfModules.toSheaf
              (associatedStructureSheaf X StandardTopology.fppf)).obj
            (RingedSite.Module.carrierLift (associatedRingedSite X StandardTopology.fppf) F))))

end AlgebraicGeometry.GroupoidsOver
