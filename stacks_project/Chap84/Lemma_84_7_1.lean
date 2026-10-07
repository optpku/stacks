module

import StacksCheckRecall
public import stacks_project.Chap84.Lemma_84_7_1_Carrier
public import stacks_project.Chap84.Lemma_84_7_1_Comparison
public import stacks_project.Chap84.Lemma_84_7_1_Ringed
public import stacks_project.Chap84.Lemma_84_7_1_Sections

/-!
# Lemma 84.7.1

Quasi-coherent modules on an algebraic space extend to fpqc/fppf/étale sheaves
on `(Spaces/X)` by the sections rule `F^a(Y) = Γ(Y, f^* F)`, identified with
`π_X^* F` and `a_X^* F`.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.AssociatedModule
open AlgebraicGeometry.AlgebraicSpace.Fppf

noncomputable section

universe u

/- Lemma 84.7.1 (1): the associated abelian-group rule is a sheaf for fpqc
coverings on `(Spaces/X)_étale`. -/
@[stacks 0DGN] #check associatedPresheaf_isSheaf_fpqc

/- Lemma 84.7.1 (2): the associated abelian-group rule is a sheaf for fppf
coverings, a fortiori. -/
@[stacks 0DGN] #check associatedPresheaf_isSheaf_fppf

/- Lemma 84.7.1 (3): the associated abelian-group rule is a sheaf for étale
coverings, a fortiori. -/
@[stacks 0DGN] #check associatedPresheaf_isSheaf_etale

/- Lemma 84.7.1 (4): `F^a = π_X^* F` on `(Spaces/X)_étale`. -/
@[stacks 0DGN] #check piPullbackIso

/- Lemma 84.7.1 (5): `F^a = a_X^* F` on `(Spaces/X)_fppf`. -/
@[stacks 0DGN] #check aPullbackIso

/- Lemma 84.7.1 (6): `F ↦ F^a` is an equivalence between quasi-coherent
`𝒪_X`-modules and quasi-coherent modules on `((Spaces/X)_étale, 𝒪)`. -/
@[stacks 0DGN] #check associatedFunctor_etale_isEquivalence

/- Lemma 84.7.1 (7): `F ↦ F^a` is an equivalence between quasi-coherent
`𝒪_X`-modules and quasi-coherent modules on `((Spaces/X)_fppf, 𝒪)`. -/
@[stacks 0DGN] #check associatedFunctor_fppf_isEquivalence

/- Lemma 84.7.1 (8): `ε_{X,*} a_X^* F = π_X^* F`. -/
@[stacks 0DGN] #check epsilon_pushforward_aPullbackIso

/- Lemma 84.7.1 (9): `a_{X,*} a_X^* F = F`. -/
@[stacks 0DGN] #check a_pushforward_aPullbackIso

/- Lemma 84.7.1 (10): `R^i ε_{X,*}(a_X^* F) = 0` for `i > 0`. -/
@[stacks 0DGN] #check epsilon_higherDirectImage_vanishes

/- Lemma 84.7.1 (11): `R^i a_{X,*}(a_X^* F) = 0` for `i > 0`. -/
@[stacks 0DGN] #check a_higherDirectImage_vanishes

end

end
