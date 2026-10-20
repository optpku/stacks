/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.SplitEpiFactorization

@[expose] public section

/-!
# Functorial split-epimorphic mapping-cocone factorizations

This leaf packages the split-epimorphic mapping-cocone factorization as a functor on the arrow
category.  Its three structural maps form natural transformations to and from the endpoint
functors, so downstream constructions can use the factorization without unfolding its biproduct
model.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CochainComplex.SplitEpiFactorization

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The functor sending a cochain map to its canonical split-epimorphic mapping-cocone
factorization object. -/
@[stacks 0642 "functorial split-epimorphic mapping-cocone factorization"]
noncomputable def functor :
    Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ where
  obj α := obj α.left α.right
  map f := map f.left f.right
  map_id α := map_id α.left α.right
  map_comp f g := map_comp f.left f.right g.left g.right

/-- The factorization functor evaluates to the canonical mapping-cocone factorization object. -/
@[simp, stacks 0642 "split-epimorphic factorization functor object formula"]
theorem functor_obj (α : Arrow (CochainComplex C ℤ)) :
    functor.obj α = SplitEpiFactorization.obj α.left α.right := sorry

/-- The factorization functor maps a commuting square by the canonical map between its
factorization objects. -/
@[simp, stacks 0642 "split-epimorphic factorization functor map formula"]
theorem functor_map {α β : Arrow (CochainComplex C ℤ)} (f : α ⟶ β) :
    functor.map f = SplitEpiFactorization.map f.left f.right := sorry

namespace Functorial

/-- The source projection is natural in commutative squares of cochain maps. -/
@[stacks 0642 "naturality of the split-epimorphic factorization projection"]
theorem projection_naturality
    {α β : Arrow (CochainComplex C ℤ)} (f : α ⟶ β) :
    functor.map f ≫ SplitEpiFactorization.projection β.left β.right =
      SplitEpiFactorization.projection α.left α.right ≫ Arrow.leftFunc.map f := sorry

/-- The natural projection from the factorization functor to the source-endpoint functor. -/
@[stacks 0642 "natural projection from split-epimorphic factorizations"]
noncomputable def projection :
    functor ⟶
      (Arrow.leftFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) where
  app α := SplitEpiFactorization.projection α.left α.right
  naturality _ _ f := map_comp_projection f.left f.right

/-- The component of the natural factorization projection is the canonical biproduct
projection. -/
@[simp, stacks 0642 "natural factorization projection component"]
theorem projection_app (α : Arrow (CochainComplex C ℤ)) :
    projection.app α = SplitEpiFactorization.projection α.left α.right := sorry

/-- The source section is natural in commutative squares of cochain maps. -/
@[stacks 0642 "naturality of the split-epimorphic factorization section"]
theorem section_naturality
    {α β : Arrow (CochainComplex C ℤ)} (f : α ⟶ β) :
    Arrow.leftFunc.map f ≫ SplitEpiFactorization.section_ β.left β.right =
      SplitEpiFactorization.section_ α.left α.right ≫ functor.map f := sorry

/-- The natural section from the source-endpoint functor to the factorization functor. -/
@[stacks 0642 "natural section into split-epimorphic factorizations"]
noncomputable def section_ :
    (Arrow.leftFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) ⟶
      functor where
  app α := SplitEpiFactorization.section_ α.left α.right
  naturality _ _ f := (section_comp_map f.left f.right).symm

/-- The component of the natural factorization section is the canonical biproduct inclusion. -/
@[simp, stacks 0642 "natural factorization section component"]
theorem section_app (α : Arrow (CochainComplex C ℤ)) :
    section_.app α = SplitEpiFactorization.section_ α.left α.right := sorry

/-- The factorization map to the target is natural in commutative squares of cochain maps. -/
@[stacks 0642 "naturality of the split-epimorphic factorization map"]
theorem desc_naturality
    {α β : Arrow (CochainComplex C ℤ)} (f : α ⟶ β) :
    functor.map f ≫ SplitEpiFactorization.desc β.hom =
      SplitEpiFactorization.desc α.hom ≫ Arrow.rightFunc.map f := sorry

/-- The natural map from the factorization functor to the target-endpoint functor. -/
@[stacks 0642 "natural split-epimorphic factorization map"]
noncomputable def desc :
    functor ⟶
      (Arrow.rightFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) where
  app α := SplitEpiFactorization.desc α.hom
  naturality _ _ f :=
    SplitEpiFactorization.desc_naturality f.left f.right (Arrow.w f).symm

/-- The component of the natural factorization map is the canonical split epimorphism. -/
@[simp, stacks 0642 "natural split-epimorphic factorization map component"]
theorem desc_app (α : Arrow (CochainComplex C ℤ)) :
    desc.app α = SplitEpiFactorization.desc α.hom := sorry

/-- The natural section followed by the natural projection is the identity of the source-endpoint
functor. -/
@[simp, stacks 0642 "natural split-epimorphic projection-section computation"]
theorem section_comp_projection :
    section_ ≫ projection =
      𝟙 (Arrow.leftFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) := sorry

/-- The natural section followed by the factorization map recovers the original arrow. -/
@[stacks 0642 "functorial split-epimorphic factorization equation"]
theorem section_comp_desc :
    section_ ≫ desc =
      (Arrow.leftToRight :
        (Arrow.leftFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) ⟶
          Arrow.rightFunc) := sorry

end Functorial

end CochainComplex.SplitEpiFactorization
