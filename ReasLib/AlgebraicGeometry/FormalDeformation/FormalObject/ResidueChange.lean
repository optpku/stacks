module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Cofibered
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue
public import ReasLib.RingTheory.Smooth.Adic.Basic

/-!
# Versal formal objects after change of residue field

Versal formal objects extend along finite residue-field extensions over a
formally smooth map of complete local bases.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k l : Type u} [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

/-- A versal formal object extends after a finite residue-field extension to a
versal formal object over a complete local algebra, with a local map of bases
that is formally smooth for the target maximal-ideal-adic topology and induces
the prescribed extension on residue fields. -/
@[stacks 0DQF]
theorem exists_isVersal_residueChangeOver [Functor.IsFibered.InGroupoids p.op]
    (ξ : FormalObject p) [IsVersal ξ] :
    ∃ (S : CompleteLocalAlgCat Λ l) (f : ξ.base.carrier →ₐ[Λ] S.carrier),
      IsLocalHom f ∧
        f.toRingHom.formally_smooth_for_adic (IsLocalRing.maximalIdeal S.carrier) ∧
        (CompleteLocalAlgCat.residueHom S).hom.comp f =
          (IsScalarTower.toAlgHom Λ k l).comp (CompleteLocalAlgCat.residueHom ξ.base).hom ∧
        ∃ η : FormalObject (ArtinianLocalAlgCat.residueChangeOver Λ k l p),
          η.base = S ∧ IsVersal η :=
  sorry

end FormalObject
