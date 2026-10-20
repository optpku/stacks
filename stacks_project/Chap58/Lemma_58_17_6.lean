/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.17.6 (1): if `X` is a Noetherian scheme and every finite locally free
`𝒪_X`-module is complete along the infinitesimal neighbourhoods of a closed subscheme
`Y ⊂ X`, then restriction `FÉt_X → FÉt_Y` is fully faithful. -/
@[stacks 0EJZ] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_finiteLocallyFree_sections :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
      (∀ E : RingedSpace.Coh X.toRingedSpace,
        CoherentCompletion.finiteLocallyFree X E →
          Function.Bijective (CoherentCompletion.sectionsComparison I E.obj)) →
        Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful)

/- Lemma 58.17.6 (2): if `X` is a Noetherian scheme with an ample invertible module `L`
whose nonnegative tensor powers are eventually complete along the infinitesimal
neighbourhoods of a closed subscheme `Y ⊂ X`, then restriction `FÉt_X → FÉt_Y` is fully
faithful. -/
@[stacks 0EJZ] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_ample_sections :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (L : X.Modules),
      Modules.isAmpleObject L →
        (∃ m₀ : ℕ, ∀ m ≥ m₀,
          Function.Bijective
            (CoherentCompletion.sectionsComparison I (RingedSpace.TensorPower.sheaf L m))) →
        Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful)

/- Lemma 58.17.6 (3): if `X` is a Noetherian quasi-affine scheme and global sections of
`𝒪_X` map isomorphically to the inverse limit of sections on the infinitesimal
neighbourhoods of a closed subscheme `Y ⊂ X`, then restriction `FÉt_X → FÉt_Y` is fully
faithful. -/
@[stacks 0EJZ] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_quasiAffine_sections :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (hX : X.IsQuasiAffine),
      Function.Bijective
        (CoherentCompletion.sectionsComparison I (SheafOfModules.unit X.ringCatSheaf)) →
        Nonempty (finiteEtaleBaseChange I.subschemeι).FullyFaithful)

end AlgebraicGeometry.Scheme
