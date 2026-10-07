module

public import stacks_project.Chap103.Lemma_103_15_3_Comparison

/-!
With the assumptions and notation of Lemma 103.15.1, the canonical base-change
map `g⁻¹ Rf_* F ⟶ Rf'_*(g')⁻¹ F` is an isomorphism for every abelian sheaf `F`
on `X_étale` (resp. `X_fppf`).
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory CategoryTheory.Abelian
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable (f : X ⟶ Y)

section Smooth

variable [Smooth f]
variable [HasSheafify X.etaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf X.etaleTopology AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1})]
variable (F : Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)

/-- Lemma 103.15.3 (1): with the assumptions and notation of Lemma 103.15.1,
the canonical base-change map `g⁻¹ Rf_* F ⟶ Rf'_*(g')⁻¹ F` is an isomorphism
for every abelian sheaf `F` on `X_étale`. -/
@[stacks 0GR3]
instance lisseEtaleHigherDirectImageRestrictionComparison.instIsIso :
    IsIso (lisseEtaleHigherDirectImageRestrictionComparison f F p) :=
  sorry

end Smooth

section Flat

variable [Flat f]
variable [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (inheritedFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1})]
variable (F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)

/-- Lemma 103.15.3 (2): with the assumptions and notation of Lemma 103.15.1,
the canonical base-change map `g⁻¹ Rf_* F ⟶ Rf'_*(g')⁻¹ F` is an isomorphism
for every abelian sheaf `F` on `X_fppf`. -/
@[stacks 0GR3]
instance flatFppfHigherDirectImageRestrictionComparison.instIsIso :
    IsIso (flatFppfHigherDirectImageRestrictionComparison f F p) :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicStack
