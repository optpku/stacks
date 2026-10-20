/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change in `CommAlgCat`

This leaf packages extension of scalars for commutative algebras through the
canonical equivalence with an under-category.  It deliberately uses the
pushout functor supplied by mathlib, rather than rebuilding tensor-product
objects or their universal properties in each consumer.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CommAlgCat.BaseChange

variable {R S : CommRingCat.{u}}

/-- Extension of scalars along a morphism of commutative rings, viewed as a
functor between categories of commutative algebras. -/
@[stacks 00QV "commutative-algebra base change"]
noncomputable abbrev functor (f : R ⟶ S) : CommAlgCat R ⥤ CommAlgCat S :=
  (commAlgCatEquivUnder R).functor ⋙ Under.pushout f ⋙
    (commAlgCatEquivUnder S).inverse

/-- Extension of scalars along `f`, followed by forgetting the resulting
algebra to its underlying commutative ring. -/
@[stacks 00QV "commutative-algebra base change"]
noncomputable abbrev forgetFunctor (f : R ⟶ S) : CommAlgCat R ⥤ CommRingCat :=
  (commAlgCatEquivUnder R).functor ⋙ Under.pushout f ⋙ Under.forget S

/-- Forgetting scalar extension from `A` to `B` gives the ordinary tensor product
of the original algebra with `B`, with the factors ordered as `R ⊗[A] B`. -/
noncomputable def forgetObjIsoTensorProduct
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (R : CommAlgCat A) :
    (forget₂ (CommAlgCat B) CommRingCat).obj
        ((functor (CommRingCat.ofHom (algebraMap A B))).obj R) ≅
      CommRingCat.of (TensorProduct A R B) :=
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj R
  -- Local instance justification (defeq pin): the under-object's canonical structure map is required to form the tensor-product comparison over A.
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  let hU : U.right = CommRingCat.of R := by
    simpa [U] using CommRingCat.mkUnder_right (CommRingCat.of A) R
  let e : U.right ≃ₐ[A] R := by
    cases hU
    refine { toRingEquiv := RingEquiv.refl _, commutes' := ?_ }
    intro a
    rfl
  let hTensor :
      (Under.forget (CommRingCat.of B)).obj
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of B)).obj U) =
        CommRingCat.of (TensorProduct A B U.right) :=
    CommRingCat.tensorProd_obj_right (CommRingCat.of A) (CommRingCat.of B) U
  eqToIso rfl ≪≫
    (Under.forget (CommRingCat.of B)).mapIso
      ((CommRingCat.tensorProdIsoPushout
        (CommRingCat.of A) (CommRingCat.of B)).app U).symm ≪≫
    eqToIso hTensor ≪≫
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) e).toRingEquiv.toCommRingCatIso ≪≫
    (Algebra.TensorProduct.comm A B R).toRingEquiv.toCommRingCatIso

/-- The diagram obtained by applying base change along `f` to every object
and morphism of `F`. -/
@[stacks 00QV "commutative-algebra base change"]
noncomputable abbrev diagram
    {I : Type v} [Category I] (f : R ⟶ S) (F : I ⥤ CommAlgCat R) :
    I ⥤ CommAlgCat S :=
  F ⋙ functor f

/-- The underlying commutative-ring diagram of the base change of `F` along
`f`. -/
@[stacks 00QV "commutative-algebra base change"]
noncomputable abbrev forgetDiagram
    {I : Type v} [Category I] (f : R ⟶ S) (F : I ⥤ CommAlgCat R) :
    I ⥤ CommRingCat :=
  F ⋙ forgetFunctor f

/-- The cocone obtained by applying base change along `f` to a cocone of
commutative `R`-algebras. -/
@[stacks 00QV "commutative-algebra base change"]
noncomputable abbrev cocone
    {I : Type v} [Category I] {F : I ⥤ CommAlgCat R}
    (f : R ⟶ S) (c : Cocone F) : Cocone (diagram f F) :=
  (commAlgCatEquivUnder S).inverse.mapCocone
    ((Under.pushout f).mapCocone ((commAlgCatEquivUnder R).functor.mapCocone c))

/-- The underlying commutative-ring cocone after base change along `f`. -/
@[stacks 00QV "commutative-algebra base change"]
noncomputable abbrev forgetCocone
    {I : Type v} [Category I] {F : I ⥤ CommAlgCat R}
    (f : R ⟶ S) (c : Cocone F) : Cocone (forgetDiagram f F) :=
  (Under.forget S).mapCocone
    ((Under.pushout f).mapCocone ((commAlgCatEquivUnder R).functor.mapCocone c))

/-- Base change along `f` preserves a chosen colimit cocone.  Its descent map
is assembled through the left-adjoint pushout functor and equivalences, so it
does not hide an existentially chosen algebra structure. -/
@[stacks 00QV "commutative-algebra base change"]
noncomputable def isColimit
    {I : Type v} [Category I] {F : I ⥤ CommAlgCat R}
    (f : R ⟶ S) (c : ColimitCocone F) : IsColimit (cocone f c.cocone) :=
  isColimitOfPreserves (commAlgCatEquivUnder S).inverse
    (isColimitOfPreserves (Under.pushout f)
      (isColimitOfPreserves (commAlgCatEquivUnder R).functor c.isColimit))

/-- For a connected indexing category, the underlying ring cocone after base
change along `f` is colimiting.  Connectedness is essential because the
underlying-ring functor does not preserve arbitrary coproducts of algebras. -/
@[stacks 00QV "connected commutative-algebra base change"]
noncomputable def forgetIsColimit
    {I : Type v} [Category I] [IsConnected I] {F : I ⥤ CommAlgCat R}
    (f : R ⟶ S) (c : ColimitCocone F) :
    IsColimit (forgetCocone f c.cocone) :=
  isColimitOfPreserves (Under.forget S)
    (isColimitOfPreserves (Under.pushout f)
      (isColimitOfPreserves (commAlgCatEquivUnder R).functor c.isColimit))

end CommAlgCat.BaseChange
