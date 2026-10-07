module

public import ReasLib.CategoryTheory.DerivedCategory.Concentrated.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Single-Degree Pieces of Derived Truncations

The degree-`n` successive-truncation piece is Mathlib's canonical functor
`t.truncLTGE n (n + 1)`, lifted to the full subcategory of objects concentrated
in degree `n`.  Its upper-first presentation is inherited from
`t.truncGELTIsoLTGE n (n + 1)`.

For homology, this module exposes the two canonical maps to the common lower-
truncation homology functor.  It deliberately records only natural
transformations and `IsIso` propositions: no inverse or natural isomorphism is
chosen from the deferred homology-invariance proofs.
-/

open CategoryTheory
open DerivedCategory.TStructure

universe w v u

noncomputable section

namespace CategoryTheory.DerivedCategory.Truncation.Piece

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical successive-truncation object in degree `n` is concentrated
in that degree. -/
@[stacks 08J5]
theorem obj_mem (n : ℤ) (K : DerivedCategory 𝒜) :
    concentrated 𝒜 n ((t.truncLTGE n (n + 1)).obj K) := sorry

/-- The degree-`n` successive-truncation piece, valued in the canonical full
subcategory of degree-`n` concentrated objects. -/
@[stacks 08J5]
noncomputable def functor (n : ℤ) :
    DerivedCategory 𝒜 ⥤ DerivedCategory.Concentrated 𝒜 n :=
  (concentrated 𝒜 n).lift (t.truncLTGE n (n + 1))
    (obj_mem 𝒜 n)

/-- The underlying object of the bundled degree piece is Mathlib's canonical
successive truncation. -/
@[simp, stacks 08J5]
theorem functor_obj_obj (n : ℤ) (K : DerivedCategory 𝒜) :
    ((functor 𝒜 n).obj K).obj = (t.truncLTGE n (n + 1)).obj K := sorry

/-- The underlying map of the bundled degree-piece functor is the map of
Mathlib's canonical successive-truncation functor. -/
@[simp, stacks 08J5]
theorem functor_map_hom (n : ℤ) {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    ((functor 𝒜 n).map f).hom = (t.truncLTGE n (n + 1)).map f := sorry

/-- Forgetting the concentrated-object structure recovers Mathlib's canonical
`t.truncLTGE n (n + 1)` functor. -/
@[stacks 08J5]
noncomputable def compιIso (n : ℤ) :
    functor 𝒜 n ⋙ DerivedCategory.Concentrated.ι 𝒜 n ≅
      t.truncLTGE n (n + 1) :=
  (concentrated 𝒜 n).liftCompιIso (t.truncLTGE n (n + 1))
    (obj_mem 𝒜 n)

namespace compιIso

/-- The forward component of the concentrated-piece inclusion comparison is
the identity on the underlying successive truncation. -/
@[simp, stacks 08J5]
theorem hom_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (compιIso 𝒜 n).hom.app K =
      𝟙 ((t.truncLTGE n (n + 1)).obj K) := sorry

/-- The inverse component of the concentrated-piece inclusion comparison is
the identity on the underlying successive truncation. -/
@[simp, stacks 08J5]
theorem inv_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (compιIso 𝒜 n).inv.app K =
      𝟙 ((t.truncLTGE n (n + 1)).obj K) := sorry

end compιIso

/-- The upper-first successive truncation is naturally the underlying object
of the canonical degree-`n` piece. -/
@[stacks 08J5]
noncomputable def upperIso (n : ℤ) :
    t.truncGELT n (n + 1) ≅
      functor 𝒜 n ⋙ DerivedCategory.Concentrated.ι 𝒜 n :=
  t.truncGELTIsoLTGE n (n + 1) ≪≫ (compιIso 𝒜 n).symm

/-- The forward component of `upperIso` is Mathlib's canonical comparison
between the two truncation orders. -/
@[simp, stacks 08J5]
theorem upperIso_hom_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (upperIso 𝒜 n).hom.app K =
      (t.truncGELTIsoLTGE n (n + 1)).hom.app K := sorry

/-- The inverse component of the upper-first comparison is the inverse of
Mathlib's canonical truncation comparison. -/
@[simp, stacks 08J5]
theorem upperIso_inv_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (upperIso 𝒜 n).inv.app K =
      (t.truncGELTIsoLTGE n (n + 1)).inv.app K := sorry

/-- Forward naturality of the upper-first comparison, with the canonical
successive-truncation and bundled-piece maps shown explicitly. -/
@[reassoc, stacks 08J5]
theorem upperIso_hom_naturality (n : ℤ) {K L : DerivedCategory 𝒜}
    (f : K ⟶ L) :
    (t.truncGELT n (n + 1)).map f ≫ (upperIso 𝒜 n).hom.app L =
      (upperIso 𝒜 n).hom.app K ≫
        (functor 𝒜 n ⋙ DerivedCategory.Concentrated.ι 𝒜 n).map f := sorry

/-- Inverse naturality of the upper-first comparison, with the canonical
successive-truncation and bundled-piece maps shown explicitly. -/
@[reassoc, stacks 08J5]
theorem upperIso_inv_naturality (n : ℤ) {K L : DerivedCategory 𝒜}
    (f : K ⟶ L) :
    (functor 𝒜 n ⋙ DerivedCategory.Concentrated.ι 𝒜 n).map f ≫
        (upperIso 𝒜 n).inv.app L =
      (upperIso 𝒜 n).inv.app K ≫ (t.truncGELT n (n + 1)).map f := sorry

namespace Homology

/-- The first leg of the canonical homology cospan: homology maps to the
homology of its degree-`n` lower truncation. -/
@[stacks 08J5]
noncomputable abbrev toGE (n : ℤ) :
    DerivedCategory.homologyFunctor 𝒜 n ⟶
      t.truncGE n ⋙ DerivedCategory.homologyFunctor 𝒜 n :=
  DerivedCategory.TruncGE.homologyNatTrans 𝒜 n n

/-- A component of `Homology.toGE` is induced by the canonical lower-truncation
projection. -/
@[simp, stacks 08J5]
theorem toGE_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (toGE 𝒜 n).app K =
      (DerivedCategory.homologyFunctor 𝒜 n).map ((t.truncGEπ n).app K) := sorry

/-- Every component of `Homology.toGE` is an isomorphism. -/
@[stacks 08J5]
theorem toGE_app_isIso (n : ℤ) (K : DerivedCategory 𝒜) :
    IsIso ((toGE 𝒜 n).app K) := sorry

/-- The natural transformation `Homology.toGE` is an isomorphism, without
selecting an inverse as public data. -/
@[stacks 08J5]
theorem toGE_isIso (n : ℤ) : IsIso (toGE 𝒜 n) := sorry

namespace Ambient

/-- The second leg of the canonical homology cospan: the homology of the
degree-`n` piece maps to the homology of the preceding lower truncation. -/
@[stacks 08J5]
noncomputable def toGE (n : ℤ) :
    t.truncLTGE n (n + 1) ⋙ DerivedCategory.homologyFunctor 𝒜 n ⟶
      t.truncGE n ⋙ DerivedCategory.homologyFunctor 𝒜 n :=
  (Functor.associator (t.truncGE n) (t.truncLT (n + 1))
      (DerivedCategory.homologyFunctor 𝒜 n)).hom ≫
    Functor.whiskerLeft (t.truncGE n)
      (DerivedCategory.TruncLT.homologyNatTrans 𝒜 (n + 1) n)

/-- A component of `Ambient.toGE` is induced by the canonical
upper-truncation inclusion. -/
@[simp, stacks 08J5]
theorem toGE_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (toGE 𝒜 n).app K =
      (DerivedCategory.homologyFunctor 𝒜 n).map
        ((t.truncLTι (n + 1)).app ((t.truncGE n).obj K)) := sorry

/-- Every component of `Ambient.toGE` is an isomorphism. -/
@[stacks 08J5]
theorem toGE_app_isIso (n : ℤ) (K : DerivedCategory 𝒜) :
    IsIso ((toGE 𝒜 n).app K) := sorry

/-- The natural transformation `Ambient.toGE` is an isomorphism, without
selecting an inverse as public data. -/
@[stacks 08J5]
theorem toGE_isIso (n : ℤ) :
    IsIso (toGE 𝒜 n) := sorry

end Ambient

namespace Bundled

/-- The bundled degree-`n` piece maps on restricted homology to the homology of
the preceding lower truncation. -/
@[stacks 08J5]
noncomputable def toGE (n : ℤ) :
    functor 𝒜 n ⋙ DerivedCategory.Concentrated.homologyFunctor 𝒜 n ⟶
      t.truncGE n ⋙ DerivedCategory.homologyFunctor 𝒜 n :=
  (Functor.associator (functor 𝒜 n) (DerivedCategory.Concentrated.ι 𝒜 n)
      (DerivedCategory.homologyFunctor 𝒜 n)).inv ≫
    Functor.whiskerRight (compιIso 𝒜 n).hom
      (DerivedCategory.homologyFunctor 𝒜 n) ≫
    Ambient.toGE 𝒜 n

/-- A component of the bundled piece leg computes to the corresponding
component of the ambient successive-truncation leg. -/
@[simp, stacks 08J5]
theorem toGE_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (toGE 𝒜 n).app K = (Ambient.toGE 𝒜 n).app K := sorry

/-- Every component of the bundled piece homology leg is an isomorphism. -/
@[stacks 08J5]
theorem toGE_app_isIso (n : ℤ) (K : DerivedCategory 𝒜) :
    IsIso ((toGE 𝒜 n).app K) := sorry

/-- The bundled piece homology leg is an isomorphism of functors, without
selecting an inverse as public data. -/
@[stacks 08J5]
theorem toGE_isIso (n : ℤ) :
    IsIso (toGE 𝒜 n) := sorry

end Bundled

end Homology

end CategoryTheory.DerivedCategory.Truncation.Piece

end
