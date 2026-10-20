module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.NoDeformations
public import stacks_project.Chap57.Definition_57_15_1_Kernel
public import stacks_project.Chap57.Lemma_57_16_3

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/- Lemma 57.16.4: if `Y → S` is smooth proper over a finite-type `k`-scheme with
`k`-rational point `s`, `X = Y_s × S` is the constant family, and a relative
Fourier--Mukai kernel `K` from `X` to `Y` restricts along
`Y_s ×_S Y_s ⟶ X ×_S Y` to the diagonal kernel `Δ_{Y_s/k,*} 𝒪_{Y_s}`, then `Y`
is isomorphic to that constant family over some open neighbourhood of `s`. -/
@[stacks 0G0R]
#check (exists_isIso_restriction_of_relativeEquivalenceKernel_fiber_diagonal :
    ∀ {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType hS] [QuasiCompact hS]
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (s : S) (hs : s = σ (closedPoint k))
    (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S)
      (Quotient.mk'' K : FourierMukaiObject.constantFamily hS σ hσ Y ⟶ Y)]
    (hK : IsIsomorphic
      (FourierMukaiObject.fiberSquarePullbackKernel hS σ hσ Y K)
      (FourierMukaiObject.diagonalKernel (FourierMukaiObject.fiberOver hS σ hσ Y))),
    ∃ U : S.Opens, s ∈ U ∧ ∃
      e : (FourierMukaiObject.baseChange U.ι Y).scheme ⟶
        (FourierMukaiObject.baseChange U.ι
          (FourierMukaiObject.constantFamily hS σ hσ Y)).scheme,
      e ≫ (FourierMukaiObject.baseChange U.ι
            (FourierMukaiObject.constantFamily hS σ hσ Y)).hom =
          (FourierMukaiObject.baseChange U.ι Y).hom ∧
        IsIso e)
