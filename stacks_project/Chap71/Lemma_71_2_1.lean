/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap71.Lemma_71_2_1_Pullback
public import stacks_project.Chap71.Lemma_71_2_1_WeakAss

/-!
# Lemma 71.2.1

Weak association of a point of an algebraic space to a quasi-coherent module is
independent of the étale scheme chart and equivalent to weak association of the
maximal ideal of the étale local ring to the module stalk. On a locally
Noetherian algebraic space the associated-point variants are equivalent as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 71.2.1 (1): for a scheme `S`, an algebraic space `X` over `S`, a
quasi-coherent `𝒪_X`-module `F`, and a point `x ∈ |X|`, the following are
equivalent: `x` is weakly associated to `F` on some étale morphism from a scheme,
on every such étale morphism, and the maximal ideal of `𝒪_{X, x̄}` is a weakly
associated prime of the stalk `F_{x̄}`. -/
@[stacks 0CTW]
theorem weakAss_etaleChart_tfae (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    List.TFAE [existsEtaleWeakAss F x, forallEtaleWeakAss F x, etaleStalkWeakAss F x] :=
  sorry

/-- Lemma 71.2.1 (2): if in addition `X` is locally Noetherian, then the conditions of
`weakAss_etaleChart_tfae` are also equivalent to `x` being associated to `F` on some
étale morphism from a scheme, on every such étale morphism, and to the maximal
ideal of `𝒪_{X, x̄}` being an associated prime of the stalk `F_{x̄}`. -/
@[stacks 0CTW]
theorem associatedPoints_etaleChart_tfae (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    List.TFAE [existsEtaleWeakAss F x, forallEtaleWeakAss F x, etaleStalkWeakAss F x,
      existsEtaleAss F x, forallEtaleAss F x, etaleStalkAss F x] :=
  sorry

/-- Weak association on some étale scheme chart is equivalent to weak association on
every étale scheme chart. -/
theorem existsEtaleWeakAss_iff_forall (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    existsEtaleWeakAss F x ↔ forallEtaleWeakAss F x :=
  sorry

/-- Weak association on some étale scheme chart is equivalent to the étale-stalk
maximal-ideal condition. -/
theorem existsEtaleWeakAss_iff_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) : existsEtaleWeakAss F x ↔ etaleStalkWeakAss F x :=
  sorry

/-- Weak association on every étale scheme chart is equivalent to the étale-stalk
maximal-ideal condition. -/
theorem forallEtaleWeakAss_iff_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) : forallEtaleWeakAss F x ↔ etaleStalkWeakAss F x :=
  sorry

/-- On a locally Noetherian algebraic space, association on some étale scheme chart is
equivalent to association on every étale scheme chart. -/
theorem existsEtaleAss_iff_forall (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ forallEtaleAss F x :=
  sorry

/-- On a locally Noetherian algebraic space, association on some étale scheme chart is
equivalent to the étale-stalk associated-prime condition. -/
theorem existsEtaleAss_iff_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ etaleStalkAss F x :=
  sorry

/-- On a locally Noetherian algebraic space, association on every étale scheme chart is
equivalent to the étale-stalk associated-prime condition. -/
theorem forallEtaleAss_iff_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    forallEtaleAss F x ↔ etaleStalkAss F x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
