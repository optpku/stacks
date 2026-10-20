/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Skeleton.Degreewise
import StacksCheckRecall

/-!
@stack 018L

# Lemma 14.21.1 compatibility facade

The reusable `SimplicialObject.Truncated.skeleton.degree` API specializes Mathlib's pointwise
left Kan extension along the opposite truncated-simplex inclusion. It owns the degreewise
colimit, structure maps, and cocone-leg formulas independently of the Chapter 14 presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.skeleton.degree

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
variable (m : ℕ) (U : SimplicialObject.Truncated C m) (Δ : SimplexCategory)

/- Lemma 14.21.1 (1): degree `Δ` of `i_{m!} U` is the colimit over truncated simplices under
`Δ`. -/
@[stacks 018L "Lemma 14.21.1 (1): degreewise skeleton colimit"]
#check (isoColimit U Δ :
    U.skeleton.obj (op Δ) ≅ colimit (diagram U Δ))

variable (g : Index m Δ)

/- A simplex in the indexing category contributes through the left-Kan-extension unit followed by
the corresponding simplicial structure map. -/
@[stacks 018L "Lemma 14.21.1 (1): skeleton colimit injection"]
#check (isoColimit.injection_inv U g :
  colimit.ι (diagram U Δ) g ≫ (isoColimit U Δ).inv =
    ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left ≫
      U.skeleton.map g.hom)

/- The forward comparison satisfies the equivalent cocone-leg formula. -/
@[stacks 018L "Lemma 14.21.1 (1): skeleton cocone leg"]
#check (isoColimit.injection_hom U g :
  ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left ≫
        U.skeleton.map g.hom ≫
      (isoColimit U Δ).hom =
    colimit.ι (diagram U Δ) g)

variable (Δ' : SimplexCategory) (φ : Δ ⟶ Δ')

/- Lemma 14.21.1 (2): postcomposition with `φ.op` reindexes the colimit diagram from degree
`Δ'` to degree `Δ`. -/
@[stacks 018L "Lemma 14.21.1 (2): skeleton indexing reindexing functor"]
#check (Index.map φ : Index m Δ' ⥤ Index m Δ)

/- Lemma 14.21.1 (2): the simplicial operator `φ` induces the map between the two degreewise
colimits by reindexing costructured arrows along `φ.op`. -/
@[stacks 018L "Lemma 14.21.1 (2): skeleton map between degreewise colimits"]
#check (colimitMap U φ : colimit (diagram U Δ') ⟶ colimit (diagram U Δ))

/- In canonical colimit coordinates, the preceding map is exactly the structure map of the
skeleton simplicial object. -/
@[stacks 018L "Lemma 14.21.1 (2): skeleton structure map in colimit coordinates"]
#check (isoColimit.map U φ :
  (isoColimit U Δ').inv ≫ U.skeleton.map φ.op ≫ (isoColimit U Δ).hom =
    colimitMap U φ)

variable (g' : Index m Δ')

/- The induced map sends the injection indexed by `g'` to the injection indexed by
postcomposition with `φ.op`. -/
@[stacks 018L "Lemma 14.21.1 (2): skeleton structure map on colimit injections"]
#check (isoColimit.injection_map U φ g' :
  colimit.ι (diagram U Δ') g' ≫ (isoColimit U Δ').inv ≫
      U.skeleton.map φ.op ≫ (isoColimit U Δ).hom =
    colimit.ι (diagram U Δ) ((Index.map φ).obj g'))

end CategoryTheory.SimplicialObject.Truncated.skeleton.degree
