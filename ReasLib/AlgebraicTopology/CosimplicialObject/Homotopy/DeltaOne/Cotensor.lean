/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Functoriality
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Cotensor
public import ReasLib.CategoryTheory.Functor.IndexedProduct.Op.HomFamily

/-!
# Cotensor representation of componentwise cosimplicial homotopies

This module packages a product-free `Δ[1]`-indexed homotopy as a compatible indexed-product
family and compares it with the cotensor-valued presentation whenever the displayed cotensor
exists.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

namespace DeltaOneHomotopy

/-- The degreewise family underlying a product-free homotopy is compatible with the
cosimplicial structure maps. -/
@[stacks 0FKJ "product-free homotopy as a compatible cotensor family"]
theorem homFamily.isCompatible (H : DeltaOneHomotopy a b) :
    Functor.indexedProd.op.HomFamily.IsCompatible
      (fun n i ↦ H.hom i :
        Functor.indexedProd.op.HomFamily (Δ[1] : SSet.{0}) U V) := sorry

/-- Package a product-free homotopy as the compatible family represented by the standard
`1`-simplex cotensor. -/
@[stacks 0FKJ "compatible cotensor family of a product-free homotopy"]
def homFamily (H : DeltaOneHomotopy a b) :
    Functor.indexedProd.op.HomFamily.Compatible (Δ[1] : SSet.{0}) U V :=
  ⟨fun n i ↦ H.hom i, homFamily.isCompatible H⟩

/-- Evaluating the compatible family of a product-free homotopy recovers its displayed
simplex-indexed component. -/
@[simp, stacks 0FKJ "compatible cotensor family component"]
theorem homFamily.apply (H : DeltaOneHomotopy a b) {n : SimplexCategory}
    (i : (Δ[1] : SSet.{0}).obj (op n)) :
    H.homFamily.1 n i = H.hom i := sorry

/-- The compatible family of a precomposed homotopy is generic Hom-family precomposition. -/
@[simp, stacks 0FKJ "compatible family of a precomposed product-free homotopy"]
theorem precomp.homFamily {T : CosimplicialObject C}
    (H : DeltaOneHomotopy a b) (p : T ⟶ U) :
    (H.precomp p).homFamily =
      Functor.indexedProd.op.HomFamily.precompose.map p H.homFamily := sorry

/-- The compatible family of a postcomposed homotopy is generic Hom-family postcomposition. -/
@[simp, stacks 0FKJ "compatible family of a postcomposed product-free homotopy"]
theorem postcomp.homFamily {W : CosimplicialObject C}
    (H : DeltaOneHomotopy a b) (p : V ⟶ W) :
    (H.postcomp p).homFamily =
      Functor.indexedProd.op.HomFamily.postcompose.map p H.homFamily := sorry

/-- The compatible family of a two-sided composite is obtained by generic source and target
composition. -/
@[simp, stacks 0FKJ "compatible family of two-sided product-free homotopy composition"]
theorem precompPostcomp.homFamily {T W : CosimplicialObject C}
    (H : DeltaOneHomotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    (H.precompPostcomp p q).homFamily =
      Functor.indexedProd.op.HomFamily.precompose.map p
        (Functor.indexedProd.op.HomFamily.postcompose.map q H.homFamily) := sorry

section

variable [HasCotensor (Δ[1] : SSet.{0}) V]

/-- The cotensor-valued natural transformation assembled from a product-free homotopy. -/
@[stacks 0FKJ "cotensor-valued map of a product-free homotopy"]
def toHomotopyHom (H : DeltaOneHomotopy a b) : U ⟶ cotensor (Δ[1] : SSet) V :=
  Functor.indexedProd.op.HomFamily.toHom H.homFamily

namespace toHomotopyHom

/-- Naturality of the cotensor-valued map represented by a product-free homotopy family. -/
@[stacks 0FKJ "naturality of the cotensor-valued homotopy map"]
theorem naturality (H : DeltaOneHomotopy a b)
    {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂) :
    U.map σ ≫ Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (op n₂) ↦ H.hom i) =
      Pi.lift (fun i : (Δ[1] : SSet.{0}).obj (op n₁) ↦ H.hom i) ≫
        (cotensor (Δ[1] : SSet) V).map σ := sorry

/-- The zero endpoint equation for the cotensor-valued map assembled from a product-free
homotopy. -/
@[stacks 0FKJ "zero endpoint of the assembled cotensor homotopy"]
theorem zero_endpoint (H : DeltaOneHomotopy a b) (n : SimplexCategory) :
    (toHomotopyHom H).app n ≫
        Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 0 (op n)) = a.app n := sorry

/-- The one endpoint equation for the cotensor-valued map assembled from a product-free homotopy. -/
@[stacks 0FKJ "one endpoint of the assembled cotensor homotopy"]
theorem one_endpoint (H : DeltaOneHomotopy a b) (n : SimplexCategory) :
    (toHomotopyHom H).app n ≫
        Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 1 (op n)) = b.app n := sorry

end toHomotopyHom

/-- Assemble a product-free `Δ[1]`-indexed homotopy into the canonical cotensor-valued homotopy. -/
@[stacks 0FKJ "assemble a product-free cosimplicial homotopy"]
def toHomotopy (H : DeltaOneHomotopy a b) : Homotopy a b where
  hom := toHomotopyHom H
  zero_endpoint := toHomotopyHom.zero_endpoint H
  one_endpoint := toHomotopyHom.one_endpoint H

/-- The cotensor-valued homotopy assembled from a product-free homotopy has the original
simplex-indexed components. -/
@[simp, stacks 0FKJ "components of the assembled cotensor-valued homotopy"]
theorem toHomotopy.app (H : DeltaOneHomotopy a b)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    H.toHomotopy.app i = H.hom i := sorry

/-- Evaluate a canonical cotensor-valued homotopy to obtain its product-free component family. -/
@[stacks 0FKJ "evaluate a cotensor homotopy componentwise"]
def ofHomotopy (H : Homotopy a b) : DeltaOneHomotopy a b where
  hom i := H.app i
  zero_endpoint n := Homotopy.app.zero H n
  one_endpoint n := Homotopy.app.one H n
  naturality := sorry

/-- Evaluating a cotensor-valued homotopy recovers each of its simplex-indexed components. -/
@[simp, stacks 0FKJ "components of the evaluated product-free homotopy"]
theorem ofHomotopy.hom (H : Homotopy a b)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (ofHomotopy H).hom i = H.app i := sorry

namespace equiv

/-- Evaluating the assembled cotensor-valued homotopy recovers the original product-free family. -/
@[simp, stacks 0FKJ "product-free homotopy comparison left inverse"]
theorem left_inv (H : DeltaOneHomotopy a b) :
    ofHomotopy H.toHomotopy = H := sorry

/-- Assembling the evaluation family of a canonical homotopy recovers that homotopy. -/
@[simp, stacks 0FKJ "product-free homotopy comparison right inverse"]
theorem right_inv (H : Homotopy a b) :
    (ofHomotopy H).toHomotopy = H := sorry

end equiv

/-- When the displayed `Δ[1]` cotensor exists, product-free and cotensor-valued cosimplicial
homotopies are equivalent. -/
@[stacks 0FKJ "product-free and cotensor-valued homotopy comparison"]
def equiv (a b : U ⟶ V) : DeltaOneHomotopy a b ≃ Homotopy a b where
  toFun := toHomotopy
  invFun := ofHomotopy
  left_inv := equiv.left_inv
  right_inv := equiv.right_inv

/-- The forward map of the comparison equivalence assembles a product-free homotopy. -/
@[simp, stacks 0FKJ "forward map of the cosimplicial homotopy comparison"]
theorem equiv.apply (H : DeltaOneHomotopy a b) :
    equiv a b H = H.toHomotopy := sorry

/-- The inverse map of the comparison equivalence evaluates a cotensor-valued homotopy. -/
@[simp, stacks 0FKJ "inverse map of the cosimplicial homotopy comparison"]
theorem equiv.symm_apply (H : Homotopy a b) :
    (equiv a b).symm H = ofHomotopy H := sorry

end

end DeltaOneHomotopy

end CategoryTheory.CosimplicialObject
