module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.NatRestriction

/-!
# Homology of a flat divided-power chain-DGA base change

For a supplied scalar-extension model `X` and a flat map `algebraMap R S`, the integer homology
of `X.algebra` in every nonnegative degree is canonically the extension of scalars of the source
integer homology.  The comparison is assembled entirely from the natural-complex model
comparison, flat extension of scalars commuting with homology, and the canonical passage from
natural to integer degrees.

The construction is natural under the canonical comparison of two supplied base-change models.
Consequently, degreewise homology vanishing and positive-homology vanishing pass to every
explicit flat base-change model without choosing a model.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DividedPowerChainAlgebra.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {A : DividedPowerChainAlgebra.{u, u} R}

/-- Tag 09PQ: for a flat scalar map, nonnegative integer homology of an explicit base-change
model is canonically the scalar extension of source integer homology. -/
@[stacks 09PQ "homology of a flat divided-power chain-DGA base change"]
noncomputable def flatHomologyIso
    (X : BaseChange (R' := S) A) (h_flat : (algebraMap R S).Flat) (n : ℕ) :
    X.algebra.toChainDGAlgebra.homology (n : ℤ) ≅
      (ModuleCat.extendScalars (algebraMap R S)).obj
        (A.toChainDGAlgebra.homology (n : ℤ)) :=
  (NatRestriction.integerHomologyIso X n).symm ≪≫
    ModuleCat.extendScalarsHomologyIso (algebraMap R S) h_flat
      A.toChainDGAlgebra.natRestriction n ≪≫
      (ModuleCat.extendScalars (algebraMap R S)).mapIso
        (A.toChainDGAlgebra.natRestrictionHomologyIso n)

/-- The forward flat homology comparison is the composite of the model comparison, the flat
homology comparison, and scalar extension of the natural-to-integer comparison. -/
theorem flatHomologyIso_hom
    (X : BaseChange (R' := S) A) (h_flat : (algebraMap R S).Flat) (n : ℕ) :
    (flatHomologyIso X h_flat n).hom =
      (NatRestriction.integerHomologyIso X n).inv ≫
        (ModuleCat.extendScalarsHomologyIso (algebraMap R S) h_flat
          A.toChainDGAlgebra.natRestriction n).hom ≫
          (ModuleCat.extendScalars (algebraMap R S)).map
            (A.toChainDGAlgebra.natRestrictionHomologyIso n).hom := sorry

/-- Tag 09PQ: the flat homology identifications commute with the canonical comparison between
two supplied scalar-extension models. -/
@[stacks 09PQ "model naturality of flat base-change homology"]
theorem flatHomologyIso_hom_naturality
    (X Y : BaseChange (R' := S) A) (h_flat : (algebraMap R S).Flat) (n : ℕ) :
    HomologicalComplex.homologyMap
          (X.chainComparison Y).toChainHom.toChainMap (n : ℤ) ≫
        (flatHomologyIso Y h_flat n).hom =
      (flatHomologyIso X h_flat n).hom := sorry

/-- Tag 09PQ: homology vanishing in one nonnegative degree passes to an explicit flat
base-change model. -/
@[stacks 09PQ "degreewise homology vanishing under flat base change"]
theorem homologyIsZero_of_flat
    (X : BaseChange (R' := S) A) (h_flat : (algebraMap R S).Flat) (n : ℕ)
    (h : IsZero (A.toChainDGAlgebra.homology (n : ℤ))) :
    IsZero (X.algebra.toChainDGAlgebra.homology (n : ℤ)) := sorry

/-- Tag 09PQ: vanishing of all positive source homology passes to an explicit flat base-change
model. -/
@[stacks 09PQ "positive homology vanishing under flat base change"]
theorem positiveHomologyVanishes_of_flat
    (X : BaseChange (R' := S) A) (h_flat : (algebraMap R S).Flat)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) :
    X.algebra.toChainDGAlgebra.PositiveHomologyVanishes := sorry

end DividedPowerChainAlgebra.BaseChange
