module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.NoDeformations

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 57.16.5: if `k` is algebraically closed, `X` is smooth proper over `k`,
`Y → S` is smooth proper with `S` of finite type over `k`, and `K` is a Fourier--Mukai
kernel of a relative equivalence from `X × S` to `Y` over `S`, then `S` is covered by
opens `U` such that `Y|_U` is `U`-isomorphic to `Y₀ × U` for some `Y₀` smooth proper
over `k`. -/
@[stacks 0G0S]
#check (FourierMukaiObject.exists_openCover_locallyProductOfSmoothProper :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {S : Scheme.{u}}
    (hS : S ⟶ Spec (.of k)) [LocallyOfFiniteType hS] [QuasiCompact hS]
    (X : FourierMukaiObject (Spec (.of k))) (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.baseChange hS X).hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S)
      (Quotient.mk'' K : FourierMukaiObject.baseChange hS X ⟶ Y)],
    ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ Y0 : FourierMukaiObject (Spec (.of k)),
        ∃ e : (FourierMukaiObject.baseChange U.ι Y).scheme ⟶
            (FourierMukaiObject.baseChange U.ι
              (FourierMukaiObject.baseChange hS Y0)).scheme,
          e ≫ (FourierMukaiObject.baseChange U.ι
                (FourierMukaiObject.baseChange hS Y0)).hom =
              (FourierMukaiObject.baseChange U.ι Y).hom ∧
            IsIso e)
