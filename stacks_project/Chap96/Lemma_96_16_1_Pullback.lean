module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_9_2_Pullback

/-!
# Inverse-image sheaves along an object of a groupoid fibration

An abelian or `A`-valued sheaf `F` on `𝒳_τ` pulls back along an object `x`
lying over `U` to the sheaf `x⁻¹ F` on `(Sch/U)_τ`, by packaging the
presheaf `pullbackPresheaf` of Definition 96.9.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

noncomputable section

universe u a b

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {𝒳 : GroupoidsOver S}

/-- The inverse-image sheaf `x⁻¹ F` on `(Sch/U)_τ`, with `U = p(x)`, obtained by
packaging `pullbackPresheaf x F.obj`. -/
def pullbackSheaf {A : Type a} [Category.{b} A] (τ : StandardTopology)
    (x : 𝒳.total) (F : Sheaf (𝒳.associatedTopology τ) A) :
    Sheaf (τ.overTopology (𝒳.p.obj x).left) A where
  obj := pullbackPresheaf x F.obj
  property := sorry

/-- The underlying presheaf of `pullbackSheaf τ x F` is `pullbackPresheaf x F.obj`. -/
theorem pullbackSheaf_obj {A : Type a} [Category.{b} A] (τ : StandardTopology)
    (x : 𝒳.total) (F : Sheaf (𝒳.associatedTopology τ) A) :
    (pullbackSheaf τ x F).obj = pullbackPresheaf x F.obj :=
  sorry

/-- `pullbackSheaf` is presheaf inverse image of `F` along `yonedaEval x`. -/
theorem pullbackSheaf_eq {A : Type a} [Category.{b} A] (τ : StandardTopology)
    (x : 𝒳.total) (F : Sheaf (𝒳.associatedTopology τ) A) :
    (pullbackSheaf τ x F).obj = (presheafInverseImage (yonedaEval x) A).obj F.obj :=
  sorry

end AlgebraicGeometry.GroupoidsOver
