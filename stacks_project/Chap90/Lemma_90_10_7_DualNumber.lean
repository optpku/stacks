module

public import stacks_project.Chap90.Definition_90_10_1_DualNumber

/-!
# Canonical residue morphisms in `ArtinianLocalAlgCat`

Every object of `C_Λ` has a canonical morphism to the residue field `k`, obtained from
the residue map and the chosen residue-field identification.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The canonical morphism `A ⟶ residue Λ k` in `ArtinianLocalAlgCat`, given by the residue
map composed with the residue-field identification of `A`. -/
noncomputable def toResidue (A : ArtinianLocalAlgCat Λ k) : A ⟶ residue Λ k where
  hom := A.residueFieldIso.toAlgHom.comp (Ideal.Quotient.mkₐ Λ (maximalIdeal A.carrier))
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `toResidue` is the residue identification of `A`. -/
theorem toResidue_hom (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A).hom =
      A.residueFieldIso.toAlgHom.comp (Ideal.Quotient.mkₐ Λ (maximalIdeal A.carrier)) := sorry

/-- `toResidue A` is a local `Λ`-algebra map compatible with residue identifications. -/
theorem toResidue_spec (A : ArtinianLocalAlgCat Λ k) :
    IsLocalHom (toResidue A).hom ∧
      (residue Λ k).residueFieldIso.toAlgHom.comp (ResidueField.mapAlgHom (toResidue A).hom) =
        A.residueFieldIso.toAlgHom := sorry

end ArtinianLocalAlgCat
