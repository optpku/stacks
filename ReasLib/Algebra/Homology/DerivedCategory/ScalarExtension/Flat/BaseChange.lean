module

public import ReasLib.Algebra.Category.ModuleCat.Tor.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat tensor-product base change

@stack 0DJD

This leaf records the explicit ring maps and the derived-homology comparison used in
Lemma 15.61.5.  The tensor-product maps are concrete; flatness and invertibility are
separate proposition-valued statements.
-/

@[expose] public section

open CategoryTheory Algebra.TensorProduct
open scoped TensorProduct

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange

variable {R R' A B A' B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [CommRing A'] [CommRing B']
variable [Algebra R R'] [Algebra R A] [Algebra R B]
variable [Algebra R' A'] [Algebra R' B']
variable [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
variable [IsScalarTower R R' A'] [Algebra R B'] [IsScalarTower R R' B']
variable [Module.Flat R R']

/-- The source tensor-product ring in the flat base-change square. -/
@[stacks 0DJD "source ring of a flat tensor-product square"]
abbrev sourceRing : Type u := A ⊗[R] B

/-- The target tensor-product ring in the flat base-change square. -/
@[stacks 0DJD "target ring of a flat tensor-product square"]
abbrev targetRing : Type u := A' ⊗[R'] B'

/-- The intermediate left base-change ring. -/
@[stacks 0DJD "left intermediate ring in flat base change"]
abbrev leftBaseRing : Type u := A ⊗[R] R'

/-- The intermediate right base-change ring. -/
@[stacks 0DJD "right intermediate ring in flat base change"]
abbrev rightBaseRing : Type u := R' ⊗[R] B

/-- The left factor map `A → A' ⊗[R'] B'`, viewed as an `R`-algebra map. -/
@[stacks 0DJD "left factor map in flat base change"]
noncomputable def leftFactorMap : A →ₐ[R] targetRing (R' := R') (A' := A') (B' := B') :=
  ((includeLeft : A' →ₐ[R'] targetRing (R' := R') (A' := A') (B' := B')).restrictScalars R).comp
    (IsScalarTower.toAlgHom R A A')

/-- The right factor map `B → A' ⊗[R'] B'` induced by a map on the normalized right factor. -/
@[stacks 0DJD "right factor map in flat base change"]
noncomputable def rightFactorMap (bMap : rightBaseRing (R := R) (R' := R') (B := B) →ₐ[R'] B') :
    B →ₐ[R] targetRing (R' := R') (A' := A') (B' := B') :=
  ((includeRight : B' →ₐ[R'] targetRing (R' := R') (A' := A') (B' := B')).restrictScalars R).comp
    ((bMap.restrictScalars R).comp
      (includeRight : B →ₐ[R] rightBaseRing (R := R) (R' := R') (B := B)))

/-- The explicit tensor-product ring map in the base-change square. -/
@[stacks 0DJD "tensor-product ring map in flat base change"]
noncomputable def productMap
    (bMap : rightBaseRing (R := R) (R' := R') (B := B) →ₐ[R'] B') :
    sourceRing (R := R) (A := A) (B := B) →+*
      targetRing (R' := R') (A' := A') (B' := B') :=
  (@Algebra.TensorProduct.productMap R (targetRing (R' := R') (A' := A') (B' := B'))
      A B inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (leftFactorMap (A := A) (A' := A') (B' := B'))
      (rightFactorMap (B := B) (B' := B') bMap)).toRingHom

/-- The left factor map used in the source flatness hypothesis. -/
@[stacks 0DJD "left tensor-product base-change map"]
noncomputable def leftBaseChangeMap :
    leftBaseRing (R := R) (R' := R') (A := A) →ₐ[R] A' :=
  Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom R A A')
    (IsScalarTower.toAlgHom R R' A')

/-- Flatness of the direct tensor-product map follows from the two source flatness hypotheses. -/
@[stacks 0DJD "flatness of the tensor-product base-change map"]
theorem productMap_flat_of_baseChange
    (bMap : rightBaseRing (R := R) (R' := R') (B := B) →ₐ[R'] B')
    (haFlat :
      letI : Algebra (leftBaseRing (R := R) (R' := R') (A := A)) A' :=
        (leftBaseChangeMap (R := R) (R' := R') (A := A) (A' := A')).toAlgebra
      Module.Flat (leftBaseRing (R := R) (R' := R') (A := A)) A')
    (hbFlat :
      letI : Algebra (rightBaseRing (R := R) (R' := R') (B := B)) B' := bMap.toAlgebra
      Module.Flat (rightBaseRing (R := R) (R' := R') (B := B)) B') :
    letI : Algebra (sourceRing (R := R) (A := A) (B := B))
        (targetRing (R' := R') (A' := A') (B' := B')) :=
      (_root_.CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange.productMap
        (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') bMap).toAlgebra
    Module.Flat (sourceRing (R := R) (A := A) (B := B))
      (targetRing (R' := R') (A' := A') (B' := B')) := sorry

/-- The flat base-change comparison on homology for the derived tensor extension. -/
@[stacks 0DJD "Lemma 15.61.5"]
theorem homologyComparison_isIso
    (bMap : rightBaseRing (R := R) (R' := R') (B := B) →ₐ[R'] B')
    (haFlat :
      letI : Algebra (leftBaseRing (R := R) (R' := R') (A := A)) A' :=
        (leftBaseChangeMap (R := R) (R' := R') (A := A) (A' := A')).toAlgebra
      Module.Flat (leftBaseRing (R := R) (R' := R') (A := A)) A')
    (hbFlat :
      letI : Algebra (rightBaseRing (R := R) (R' := R') (B := B)) B' := bMap.toAlgebra
      Module.Flat (rightBaseRing (R := R) (R' := R') (B := B)) B')
    (M : DerivedCategory (ModuleCat A)) (i : ℤ) :
    let f :=
      (_root_.CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange.productMap
        (R := R) (R' := R') (A := A) (B := B) (A' := A') (B' := B') bMap)
    IsIso (_root_.CategoryTheory.ModuleCat.derivedExtensionHomologyComparison f
      ((_root_.CategoryTheory.ModuleCat.derivedExtensionOfScalars (algebraMap A
        (sourceRing (R := R) (A := A) (B := B)))).obj M) i) := sorry

end CategoryTheory.ModuleCat.DerivedExtension.FlatBaseChange
