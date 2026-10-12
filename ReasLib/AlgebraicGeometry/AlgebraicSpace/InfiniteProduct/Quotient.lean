/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Presentation

/-!
# The sheaf quotient of the infinite product presentation

The quotient presheaf and fppf quotient sheaf of the infinite product pre-relation have a
canonical atlas and a section induced by the zeroth coordinate evaluation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteProduct

/-- The presheaf of objectwise quotients of morphisms into the product spectrum by its
pre-relation. -/
def functorOfPoints (k : Type u) [Field k] : (Over (base k))ᵒᵖ ⥤ Type u :=
  (preRelation k).quotientPresheaf

/-- The Type-u functor of points is the objectwise quotient presheaf of the pre-relation. -/
theorem functorOfPoints_eq (k : Type u) [Field k] :
    functorOfPoints k = (preRelation k).quotientPresheaf := sorry

/-- The fppf sheaf `X = U / R`, obtained by sheafifying the universe-raised quotient presheaf. -/
def sheafOfPoints (k : Type u) [Field k] :
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)) :=
  (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k))

/-- `sheafOfPoints k` is the fppf quotient sheaf of the infinite product pre-relation. -/
theorem sheafOfPoints_eq (k : Type u) [Field k] :
    sheafOfPoints k = (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k)) := sorry

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas (k : Type u) [Field k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶ sheafOfPoints k :=
  (preRelation k).quotientMap (Scheme.fppfTopology.over (base k))

/-- The atlas is the canonical fppf quotient map of the pre-relation. -/
theorem atlas_eq (k : Type u) [Field k] :
    atlas k = (preRelation k).quotientMap (Scheme.fppfTopology.over (base k)) := sorry

/-- The atlas `U ⟶ X` is representable and étale with respect to `uliftYoneda`. -/
theorem atlas_etale (k : Type u) [Field k] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom := sorry

/-- The atlas `U ⟶ X` is étale-locally surjective. -/
theorem atlas_locallySurjective (k : Type u) [Field k] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom := sorry

/-- The diagonal of the fppf quotient sheaf `X = U / R` is representable. -/
theorem representableDiagonal_sheafOfPoints (k : Type u) [Field k] :
    uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := sorry

/-- The fppf quotient sheaf `X = U / R` is an algebraic space over `S`: it has a representable
étale locally-surjective atlas from `U` and a representable diagonal. -/
theorem sheafOfPoints_spec (k : Type u) [Field k] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := sorry

/-- The sheaf atlas of `X = U / R` has kernel pair given by the two projections of `R`. -/
theorem isKernelPair_atlas (k : Type u) [Field k] :
    IsKernelPair (atlas k)
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (preRelation k).t)
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (preRelation k).s) := sorry

/-- The presenting data of `X = U / R` is an étale equivalence relation whose sheaf atlas has
kernel pair `R`. -/
theorem presentation_spec (k : Type u) [Field k] :
    (preRelation k).IsEtaleEquivalenceRelation ∧ IsKernelPair (atlas k)
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (preRelation k).t)
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (preRelation k).s) := sorry

/-- The section `S ⟶ X` induced by `f_0`. -/
def sectionHom (k : Type u) [Field k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (Over.mk (𝟙 (base k))) ⟶
      sheafOfPoints k :=
  (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (immersionOver k 0) ≫ atlas k

/-- The section is the `uliftYoneda` image of `f_0` followed by the atlas. -/
theorem sectionHom_eq (k : Type u) [Field k] :
    sectionHom k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (immersionOver k 0) ≫
        atlas k := sorry

end AlgebraicGeometry.AlgebraicSpace.InfiniteProduct
