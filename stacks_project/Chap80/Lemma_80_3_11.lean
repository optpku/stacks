module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable

/-!
# Glueing fppf sheaves from Zariski sheaves and algebraic-space subfunctors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.3.11: if `S` is a scheme and `F` is a Zariski sheaf of sets on
`(Sch/S)_fppf`, and there is an indexed family of subfunctors `H i ⊂ F` that
are themselves fppf sheaves, whose inclusions are representable by algebraic
spaces, and whose coproduct map `Sigma.desc (fun i ↦ (H i).ι)` is locally
surjective after fppf sheafification, then `F` is an fppf sheaf. -/
@[stacks 07WE]
theorem isSheaf_fppf_of_zariski_subfunctors {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    {I : Type u} (H : I → Subfunctor F)
    (hH_sheaf : ∀ i, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (H i).toFunctor)
    (hH_rep : ∀ i, representableByAlgebraicSpaces (H i).ι)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (Sigma.desc fun i ↦ (H i).ι)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F := sorry

end AlgebraicGeometry.AlgebraicSpace
