/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedCoproduct
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Tensor products of indexed coproducts

This file isolates the Fubini existence API for indexed coproduct functors.  A coproduct indexed
by a pointwise product exists whenever the corresponding iterated indexed coproduct exists.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe w i d v u

namespace CategoryTheory.Functor

variable {D : Type i} [Category.{d} D] {C : Type u} [Category.{v} C]

namespace HasIndexedCoprod

/-- An iterated indexed coproduct supplies the indexed coproduct whose index functor is the
pointwise tensor product.  This is the canonical fixed-functor orientation of coproduct Fubini:
`V` is the inner index and `U` is the outer index. -/
@[stacks 017L "Fubini existence for indexed coproducts"]
instance (priority := 40) tensor
    (U V : Dᵒᵖ ⥤ Type w) (X : Dᵒᵖ ⥤ C)
    [HasIndexedCoprod V X] [HasIndexedCoprod U (indexedCoprod V X)] :
    HasIndexedCoprod (U ⊗ V) X :=
  ⟨fun Delta ↦
    @hasCoproduct_of_equiv_of_iso
      ((U ⊗ V).obj Delta) (Σ _ : U.obj Delta, V.obj Delta) C _
      (fun _ : Σ _ : U.obj Delta, V.obj Delta ↦ X.obj Delta)
      (fun _ : (U ⊗ V).obj Delta ↦ X.obj Delta)
      (@instHasCoproductSigmaFstSndOfSigmaObj C _ (U.obj Delta)
        (fun _ : U.obj Delta ↦ V.obj Delta)
        (fun _ _ ↦ X.obj Delta)
        (fun _ ↦ HasIndexedCoprod.hasCoproduct (U := V) (V := X) Delta)
        (HasIndexedCoprod.hasCoproduct
          (U := U) (V := indexedCoprod V X) Delta))
      (Equiv.sigmaEquivProd (U.obj Delta) (V.obj Delta)).symm
      (fun _ ↦ Iso.refl _)⟩

end HasIndexedCoprod

namespace HasIndexedCoprods

/-- Uniform indexed coproducts by `U` and `V` construct uniform indexed coproducts by `U ⊗ V`.
This is an explicit constructor rather than an instance so fixed goals have one Fubini path. -/
@[stacks 017L "uniform Fubini existence for indexed coproducts"]
abbrev tensor (U V : Dᵒᵖ ⥤ Type w) (C : Type u) [Category.{v} C]
    [HasIndexedCoprods U C] [HasIndexedCoprods V C] :
    HasIndexedCoprods (U ⊗ V) C :=
  ⟨fun X ↦ HasIndexedCoprod.tensor U V X⟩

end HasIndexedCoprods

namespace indexedCoprod

variable (U V : Dᵒᵖ ⥤ Type w) (X : Dᵒᵖ ⥤ C)
variable [HasIndexedCoprod V X] [HasIndexedCoprod U (indexedCoprod V X)]

/-- The degreewise Fubini map from the coproduct indexed by `U ⊗ V` to the iterated indexed
coproduct, with `V` as the inner index. -/
@[stacks 017L "indexed-coproduct Fubini component"]
def tensorToIteratedApp (Delta : Dᵒᵖ) :
    (indexedCoprod (U ⊗ V) X).obj Delta ⟶
      (indexedCoprod U (indexedCoprod V X)).obj Delta :=
  Sigma.desc fun uv ↦
    Sigma.ι (fun _ : V.obj Delta ↦ X.obj Delta) uv.2 ≫
      Sigma.ι (fun _ : U.obj Delta ↦ (indexedCoprod V X).obj Delta) uv.1

/-- The degreewise Fubini components are natural in the indexing category. -/
@[stacks 017L "indexed-coproduct Fubini naturality"]
theorem tensorToIteratedApp.naturality {Delta Delta' : Dᵒᵖ} (f : Delta ⟶ Delta') :
    (indexedCoprod (U ⊗ V) X).map f ≫ tensorToIteratedApp U V X Delta' =
      tensorToIteratedApp U V X Delta ≫
        (indexedCoprod U (indexedCoprod V X)).map f := sorry

/-- The canonical morphism from a product-indexed coproduct to its iterated form. -/
@[stacks 017L "indexed-coproduct Fubini morphism"]
def tensorToIterated :
    indexedCoprod (U ⊗ V) X ⟶ indexedCoprod U (indexedCoprod V X) where
  app := tensorToIteratedApp U V X
  naturality := fun {_ _} f ↦ tensorToIteratedApp.naturality U V X f

/-- The component of the canonical morphism to the iterated indexed coproduct. -/
@[simp, stacks 017L "indexed-coproduct Fubini component formula"]
theorem tensorToIterated.app (Delta : Dᵒᵖ) :
    (tensorToIterated U V X).app Delta = tensorToIteratedApp U V X Delta := sorry

/-- The degreewise Fubini map from an iterated indexed coproduct to the coproduct indexed by
`U ⊗ V`. -/
@[stacks 017L "inverse indexed-coproduct Fubini component"]
def iteratedToTensorApp (Delta : Dᵒᵖ) :
    (indexedCoprod U (indexedCoprod V X)).obj Delta ⟶
      (indexedCoprod (U ⊗ V) X).obj Delta :=
  Sigma.desc fun u ↦
    Sigma.desc fun v ↦
      Sigma.ι (fun _ : (U ⊗ V).obj Delta ↦ X.obj Delta) (u, v)

/-- The inverse degreewise Fubini components are natural in the indexing category. -/
@[stacks 017L "inverse indexed-coproduct Fubini naturality"]
theorem iteratedToTensorApp.naturality {Delta Delta' : Dᵒᵖ} (f : Delta ⟶ Delta') :
    (indexedCoprod U (indexedCoprod V X)).map f ≫ iteratedToTensorApp U V X Delta' =
      iteratedToTensorApp U V X Delta ≫ (indexedCoprod (U ⊗ V) X).map f := sorry

/-- The canonical morphism from an iterated indexed coproduct to its product-indexed form. -/
@[stacks 017L "inverse indexed-coproduct Fubini morphism"]
def iteratedToTensor :
    indexedCoprod U (indexedCoprod V X) ⟶ indexedCoprod (U ⊗ V) X where
  app := iteratedToTensorApp U V X
  naturality := fun {_ _} f ↦ iteratedToTensorApp.naturality U V X f

/-- The component of the canonical morphism from the iterated indexed coproduct. -/
@[simp, stacks 017L "inverse indexed-coproduct Fubini component formula"]
theorem iteratedToTensor.app (Delta : Dᵒᵖ) :
    (iteratedToTensor U V X).app Delta = iteratedToTensorApp U V X Delta := sorry

/-- The two Fubini morphisms compose to the identity on the product-indexed coproduct. -/
@[stacks 017L]
theorem tensorIso.hom_inv_id :
    tensorToIterated U V X ≫ iteratedToTensor U V X =
      𝟙 (indexedCoprod (U ⊗ V) X) := sorry

/-- The two Fubini morphisms compose to the identity on the iterated indexed coproduct. -/
@[stacks 017L]
theorem tensorIso.inv_hom_id :
    iteratedToTensor U V X ≫ tensorToIterated U V X =
      𝟙 (indexedCoprod U (indexedCoprod V X)) := sorry

/-- A coproduct indexed by a pointwise tensor product is canonically the corresponding iterated
indexed coproduct. -/
@[stacks 017L "indexed-coproduct Fubini isomorphism"]
def tensorIso :
    indexedCoprod (U ⊗ V) X ≅ indexedCoprod U (indexedCoprod V X) where
  hom := tensorToIterated U V X
  inv := iteratedToTensor U V X
  hom_inv_id := tensorIso.hom_inv_id U V X
  inv_hom_id := tensorIso.inv_hom_id U V X

/-- The indexed-coproduct Fubini isomorphism is natural in the valued functor. -/
@[stacks 017L]
theorem tensorIso.naturality {Y : Dᵒᵖ ⥤ C}
    [HasIndexedCoprod V Y] [HasIndexedCoprod U (indexedCoprod V Y)]
    (f : X ⟶ Y) :
    (tensorIso U V X).hom ≫ hom U (hom V f) =
      hom (U ⊗ V) f ≫ (tensorIso U V Y).hom := sorry

end indexedCoprod

end CategoryTheory.Functor
