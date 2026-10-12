/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.SplitMonoFactorization

/-!
# Functorial split-monomorphic mapping-cone factorizations

This file packages the split-monomorphic mapping-cone factorization as a functor on the arrow
category.  Its natural inclusion and projection recover the original arrow, while the canonical
section exhibits the projection as a split epimorphism in the functor category.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.SplitMonoFactorization

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The canonical middle object of the split-monomorphic factorization, functorial in a cochain
map and in commutative squares between cochain maps. -/
@[stacks 013N "split-monomorphic factorization functor"]
def functor :
    Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ where
  obj f := obj f.left f.right
  map φ := map φ.left φ.right
  map_id f := map_id f.left f.right
  map_comp φ ψ := map_comp φ.left φ.right ψ.left ψ.right

/-- The factorization functor sends a cochain map to its canonical split-monomorphic
factorization object. -/
@[simp, stacks 013N "split-monomorphic factorization functor object formula"]
theorem functor_obj (f : Arrow (CochainComplex C ℤ)) :
    functor.obj f = obj f.left f.right := sorry

/-- The factorization functor sends a commutative square to the canonical map between its
factorization objects. -/
@[simp, stacks 013N "split-monomorphic factorization functor map formula"]
theorem functor_map {f g : Arrow (CochainComplex C ℤ)} (φ : f ⟶ g) :
    functor.map φ = map φ.left φ.right := sorry

namespace Functorial

/-- The canonical factorization inclusion is natural in commutative squares of cochain maps. -/
@[stacks 013N "naturality of the split-monomorphic factorization inclusion"]
theorem inclusion_naturality {f g : Arrow (CochainComplex C ℤ)} (φ : f ⟶ g) :
    Arrow.leftFunc.map φ ≫ ι g.hom = ι f.hom ≫ functor.map φ := sorry

/-- The source inclusions form a natural transformation into the split-monomorphic
factorization functor. -/
@[stacks 013N "natural split-monomorphic factorization inclusion"]
def inclusion :
    (Arrow.leftFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) ⟶ functor where
  app f := ι f.hom
  naturality _ _ φ := inclusion_naturality φ

/-- A component of the natural factorization inclusion is the canonical inclusion attached to
the underlying cochain map. -/
@[simp, stacks 013N "natural factorization inclusion component"]
theorem inclusion_app (f : Arrow (CochainComplex C ℤ)) :
    inclusion.app f = ι f.hom := sorry

/-- The canonical projection from the factorization object to the target is natural in
commutative squares of cochain maps. -/
@[stacks 013N "naturality of the split-monomorphic factorization projection"]
theorem projection_naturality {f g : Arrow (CochainComplex C ℤ)} (φ : f ⟶ g) :
    functor.map φ ≫ projection g.left g.right =
      projection f.left f.right ≫ Arrow.rightFunc.map φ := sorry

/-- The target projections form a natural transformation out of the split-monomorphic
factorization functor. -/
@[stacks 013N "natural split-monomorphic factorization projection"]
def projection :
    functor ⟶ (Arrow.rightFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) where
  app f := SplitMonoFactorization.projection f.left f.right
  naturality _ _ φ := projection_naturality φ

/-- A component of the natural factorization projection is the canonical projection onto the
target of the underlying cochain map. -/
@[simp, stacks 013N "natural factorization projection component"]
theorem projection_app (f : Arrow (CochainComplex C ℤ)) :
    projection.app f = SplitMonoFactorization.projection f.left f.right := sorry

/-- The canonical target section is natural in commutative squares of cochain maps. -/
@[stacks 013N "naturality of the split-monomorphic factorization section"]
theorem section_naturality {f g : Arrow (CochainComplex C ℤ)} (φ : f ⟶ g) :
    Arrow.rightFunc.map φ ≫ SplitMonoFactorization.section_ g.left g.right =
      SplitMonoFactorization.section_ f.left f.right ≫ functor.map φ := sorry

/-- The target sections form a natural transformation into the split-monomorphic factorization
functor. -/
@[stacks 013N "natural split-monomorphic factorization section"]
def section_ :
    (Arrow.rightFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) ⟶ functor where
  app f := SplitMonoFactorization.section_ f.left f.right
  naturality _ _ φ := section_naturality φ

/-- A component of the natural target section is the canonical inclusion of the target into the
factorization object. -/
@[simp, stacks 013N "natural factorization section component"]
theorem section_app (f : Arrow (CochainComplex C ℤ)) :
    section_.app f = SplitMonoFactorization.section_ f.left f.right := sorry

/-- The natural factorization inclusion followed by the natural target projection is the
tautological natural transformation from the source of an arrow to its target. -/
@[stacks 013N "functorial split-monomorphic factorization"]
theorem inclusion_comp_projection :
    inclusion ≫ projection =
      (Arrow.leftToRight :
        (Arrow.leftFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) ⟶
          Arrow.rightFunc) := sorry

/-- The natural target section followed by the natural target projection is the identity. -/
@[simp, stacks 013N "natural split-monomorphic projection retraction"]
theorem section_comp_projection :
    section_ ≫ projection =
      𝟙 (Arrow.rightFunc : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ) := sorry

end Functorial

end CochainComplex.SplitMonoFactorization
