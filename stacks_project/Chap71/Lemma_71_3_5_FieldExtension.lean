module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Field-extension base change of algebraic spaces and modules

The fibre product `Spec K ×_{Spec k} X` of an algebraic space `X` over a field `k`
is the chosen representative of `X_K`, with projections to `X` and to `Spec K`.
Pullback of modules along the source projection is the chosen `F_K`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

/-- The algebraic space `Spec K` over `Spec k` associated to a field extension `K/k`. -/
abbrev specOver (k K : Type u) [Field k] [Field K] [Algebra k K] :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  ofOver (Over.mk (AlgebraicGeometry.FieldExtension.specMap k K))

/-- `specOver k K` is the represented algebraic space of `Spec K ⟶ Spec k`. -/
theorem specOver_eq (k K : Type u) [Field k] [Field K] [Algebra k K] :
    specOver k K =
      ofOver (Over.mk (AlgebraicGeometry.FieldExtension.specMap k K)) :=
  sorry

/-- The base change of an algebraic space `X` over `Spec k` along `Spec K ⟶ Spec k`,
as the fibre product `Spec K ×_{Spec k} X` in algebraic spaces over `Spec k`. -/
abbrev baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  product (specOver k K) X

/-- The field-extension base change is the slice product with `specOver k K`. -/
theorem baseChange_eq (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    baseChange k K X = product (specOver k K) X :=
  sorry

/-- The projection from the field-extension base change back to `X`. -/
abbrev toSource (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    baseChange k K X ⟶ X :=
  productSnd (specOver k K) X

/-- The source projection of a field-extension base change is the second product
projection. -/
theorem toSource_eq (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    toSource k K X = productSnd (specOver k K) X :=
  sorry

/-- The projection from the field-extension base change to `Spec K` over `Spec k`. -/
abbrev toBase (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    baseChange k K X ⟶ specOver k K :=
  productFst (specOver k K) X

/-- The base projection of a field-extension base change is the first product
projection. -/
theorem toBase_eq (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    toBase k K X = productFst (specOver k K) X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FieldExtension

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension

open AlgebraicGeometry.AlgebraicSpace.FieldExtension

/-- The pullback of an `𝒪_X`-module to a field-extension base change. -/
abbrev baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules) :
    (AlgebraicGeometry.AlgebraicSpace.FieldExtension.baseChange k K X).Modules :=
  (pullback (toSource k K X)).obj F

/-- Module base change along a field extension is pullback along `toSource`. -/
theorem baseChange_eq (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules) :
    baseChange k K F = (pullback (toSource k K X)).obj F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension

