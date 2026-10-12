/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.Cech.TermIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat.Presheaf.Cech AlgebraicTopology

universe u v

/- 20.9.0.1: evaluating the ordinary Čech differential of an abelian presheaf at a cochain
and tuple recovers the alternating omitted-index restriction formula. -/
@[stacks 01EE]
#check (TopCat.Presheaf.Cech.termIso_hom_d_apply :
  ∀ {X : TopCat.{u}} {ι : Type v} (𝒰 : ι → TopologicalSpace.Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (TopCat.Presheaf.cechComplex 𝒰 F).X p) (σ : Fin (p + 2) → ι),
    (termIso 𝒰 F (p + 1)).hom ((TopCat.Presheaf.cechComplex 𝒰 F).d p (p + 1) s) σ =
      differentialToFun 𝒰 F p ((termIso 𝒰 F p).hom s) σ)

/- The explicit coordinate payload is the signed sum of omitted-index restrictions. -/
#check @TopCat.Presheaf.Cech.differentialToFun

/- The same identification at the morphism level, before evaluating on cochains. -/
#check @TopCat.Presheaf.Cech.termIso_comm_d

end
