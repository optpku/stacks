module

public import stacks_project.Chap90.Lemma_90_13_3_Quotient
public import stacks_project.Chap90.Lemma_90_3_5_Cotangent

/-!
# Mod-square quotients in `C_Λ`

Objects of `ArtinianLocalAlgCat Λ k` may be reduced modulo `maximalIdeal ^ 2` or
modulo `relativeDenom`, and a morphism induces the corresponding algebra maps of
quotients via `Ideal.quotientMapₐ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The quotient of an object of `ArtinianLocalAlgCat Λ k` by the square of its
maximal ideal. -/
noncomputable def modSquare (A : ArtinianLocalAlgCat Λ k) : ArtinianLocalAlgCat Λ k :=
  A.quotient (maximalIdeal A.carrier ^ 2) (Ideal.pow_le_self two_ne_zero)

/-- The carrier of `modSquare A` is `A.carrier ⧸ maximalIdeal A.carrier ^ 2`. -/
theorem modSquare_carrier (A : ArtinianLocalAlgCat Λ k) :
    (modSquare A).carrier = (A.carrier ⧸ maximalIdeal A.carrier ^ 2) := sorry

/-- `modSquare A` is the `ArtinianLocalAlgCat` quotient by `maximalIdeal A.carrier ^ 2`. -/
theorem modSquare_spec (A : ArtinianLocalAlgCat Λ k) :
    modSquare A = A.quotient (maximalIdeal A.carrier ^ 2) (Ideal.pow_le_self two_ne_zero) :=
  sorry

/-- A morphism in `ArtinianLocalAlgCat` sends the square of the source maximal ideal
into the square of the target maximal ideal. -/
theorem modSquare_map_le {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    maximalIdeal B.carrier ^ 2 ≤ (maximalIdeal A.carrier ^ 2).comap f.hom := sorry

/-- The canonical morphism `modSquare B ⟶ modSquare A` induced by `f : B ⟶ A`. -/
noncomputable def modSquareMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    modSquare B ⟶ modSquare A where
  hom := Ideal.quotientMapₐ (maximalIdeal A.carrier ^ 2) f.hom (modSquare_map_le f)
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `modSquareMap f` is the induced quotient map. -/
theorem modSquareMap_hom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    (modSquareMap f).hom =
      Ideal.quotientMapₐ (maximalIdeal A.carrier ^ 2) f.hom (modSquare_map_le f) :=
  sorry

/-- The quotient of an object of `ArtinianLocalAlgCat Λ k` by
`relativeDenom A`, i.e. by `m_Λ A + maximalIdeal A.carrier ^ 2`. -/
noncomputable def modRelative (A : ArtinianLocalAlgCat Λ k) : ArtinianLocalAlgCat Λ k :=
  A.quotient (relativeDenom A) (relativeDenom_le_maximalIdeal A)

/-- The carrier of `modRelative A` is `A.carrier ⧸ relativeDenom A`. -/
theorem modRelative_carrier (A : ArtinianLocalAlgCat Λ k) :
    (modRelative A).carrier = (A.carrier ⧸ relativeDenom A) := sorry

/-- `modRelative A` is the `ArtinianLocalAlgCat` quotient by `relativeDenom A`. -/
theorem modRelative_spec (A : ArtinianLocalAlgCat Λ k) :
    modRelative A = A.quotient (relativeDenom A) (relativeDenom_le_maximalIdeal A) :=
  sorry

/-- A morphism in `ArtinianLocalAlgCat` sends `relativeDenom` into the target
`relativeDenom`. -/
theorem relativeDenom_map_le {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    relativeDenom B ≤ (relativeDenom A).comap f.hom := sorry

/-- The canonical morphism `modRelative B ⟶ modRelative A` induced by `f : B ⟶ A`. -/
noncomputable def modRelativeMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    modRelative B ⟶ modRelative A where
  hom := Ideal.quotientMapₐ (relativeDenom A) f.hom (relativeDenom_map_le f)
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `modRelativeMap f` is the induced quotient map. -/
theorem modRelativeMap_hom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    (modRelativeMap f).hom = Ideal.quotientMapₐ (relativeDenom A) f.hom (relativeDenom_map_le f) :=
  sorry

end ArtinianLocalAlgCat
