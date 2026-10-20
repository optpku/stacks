module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.ResidueChange
import StacksCheckRecall

/-!
# Versal formal objects after change of residue field

In Situation 90.29.1, a versal formal object of `p` over a complete local base
in `CompleteLocalAlgCat Λ k` yields a mixed-residue local `Λ`-algebra map that is
formally smooth for the `m_S`-adic topology, together with a versal formal object
of `residueChangeOver p`.
-/

@[expose] public section

open CategoryTheory IsLocalRing
open ArtinianLocalAlgCat

universe u

variable {Λ k l : Type u} [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.29.6: with notation and assumptions as in Situation 90.29.1, if `ξ`
is a versal formal object for `p` lying over `ξ.base` in
`CompleteLocalAlgCat Λ k`, then there exist `S` in `CompleteLocalAlgCat Λ l` and
a local `Λ`-algebra homomorphism `ξ.base.carrier →ₐ[Λ] S.carrier` which is
formally smooth for the `m_S`-adic topology and induces the given field
extension `l / k` on residue fields, and a versal formal object of
`residueChangeOver Λ k l p` lying over `S`. -/
@[stacks 0DQF] #check (FormalObject.exists_isVersal_residueChangeOver :
  ∀ [Functor.IsFibered.InGroupoids p.op] (ξ : FormalObject p) [FormalObject.IsVersal ξ],
    ∃ (S : CompleteLocalAlgCat Λ l) (f : ξ.base.carrier →ₐ[Λ] S.carrier),
      IsLocalHom f ∧
        f.toRingHom.formally_smooth_for_adic (IsLocalRing.maximalIdeal S.carrier) ∧
        (CompleteLocalAlgCat.residueHom S).hom.comp f =
          (IsScalarTower.toAlgHom Λ k l).comp (CompleteLocalAlgCat.residueHom ξ.base).hom ∧
        ∃ η : FormalObject (ArtinianLocalAlgCat.residueChangeOver Λ k l p),
          η.base = S ∧ FormalObject.IsVersal η)
