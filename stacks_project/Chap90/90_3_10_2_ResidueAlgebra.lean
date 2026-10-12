/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Residue algebra of an object of `C_Λ`

An object `A` of `ArtinianLocalAlgCat Λ k` carries a canonical `Λ`-algebra surjection
`A.carrier → k`, obtained by composing `IsLocalRing.residue` with the chosen residue-field
identification. This makes the extended conormal sequence available on objects of `C_Λ`.
-/

@[expose] public section

open IsLocalRing

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The residue identification of an object of `C_Λ` as an `A.carrier`-algebra structure on `k`. -/
noncomputable instance algebraResidue (A : ArtinianLocalAlgCat Λ k) : Algebra A.carrier k :=
  (A.residueFieldIso.toAlgHom.toRingHom.comp (residue A.carrier)).toAlgebra

/-- The tower `Λ → A.carrier → k` for the residue identification of an object of `C_Λ`. -/
instance isScalarTower_residue (A : ArtinianLocalAlgCat Λ k) :
    IsScalarTower Λ A.carrier k := sorry

/-- The canonical residue map of an object of `C_Λ` is surjective. -/
theorem algebraMap_surjective (A : ArtinianLocalAlgCat Λ k) :
    Function.Surjective (algebraMap A.carrier k) := sorry

/-- The kernel of the residue map of an object of `C_Λ` is the maximal ideal. -/
theorem ker_algebraMap_eq_maximalIdeal (A : ArtinianLocalAlgCat Λ k) :
    RingHom.ker (algebraMap A.carrier k) = maximalIdeal A.carrier := sorry

end ArtinianLocalAlgCat
