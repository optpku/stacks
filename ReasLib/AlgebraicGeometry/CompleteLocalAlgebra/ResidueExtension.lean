module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Artinian.ResidueFactorization

/-!
# Compatibility of local algebra maps with residue-field extensions

A map of complete local algebras over a scheme induces a specified field
extension when residue-field identifications over the base carry its residue
map to the specified algebra map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra.Hom

variable {S : Scheme.{u}}

/-- An `S`-algebra map `A → A'` induces a given field extension `l / k` when
the residue fields of `A` and `A'` may be identified with `k` and `l` over
`S` so that `ResidueField.map` recovers `algebraMap k l`. -/
def InducesResidueExtension {A A' : CompleteLocalSAlgebra S} (φ : Hom A' A)
    (k l : Type u) [Field k] [Field l] [Algebra k l]
    (σk : Spec (.of k) ⟶ S) (σl : Spec (.of l) ⟶ S) : Prop :=
  ∃ (e : ResidueField A.carrier ≃+* k) (e' : ResidueField A'.carrier ≃+* l),
    residueSpecMap e ≫ A.toS = σk ∧
      residueSpecMap e' ≫ A'.toS = σl ∧
        e'.toRingHom.comp φ.residueMap =
          (algebraMap k l).comp e.toRingHom

/-- Inducing a residue-field extension unpacks to residue identifications over
`S` whose `ResidueField.map` square is `algebraMap k l`. -/
theorem inducesResidueExtension_iff {A A' : CompleteLocalSAlgebra S}
    (φ : Hom A' A) (k l : Type u) [Field k] [Field l] [Algebra k l]
    (σk : Spec (.of k) ⟶ S) (σl : Spec (.of l) ⟶ S) :
    InducesResidueExtension φ k l σk σl ↔
      ∃ (e : ResidueField A.carrier ≃+* k)
        (e' : ResidueField A'.carrier ≃+* l),
        residueSpecMap e ≫ A.toS = σk ∧
          residueSpecMap e' ≫ A'.toS = σl ∧
            e'.toRingHom.comp φ.residueMap =
              (algebraMap k l).comp e.toRingHom :=
  sorry

end AlgebraicGeometry.CompleteLocalSAlgebra.Hom
