/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry

/-- A presheaf on the fppf site over a scheme is a sheaf if it maps by a
representable-by-algebraic-spaces morphism to a sheaf. -/
theorem isSheaf_fppfTopology_over_of_relativelyRepresentableByAlgebraicSpaces
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : AlgebraicSpace.representableByAlgebraicSpaces a)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F := sorry

/-- An fppf-locally surjective family of fppf-sheaf subfunctors with
algebraic-space-representable inclusions makes a Zariski sheaf into an fppf sheaf. -/
@[stacks 07WE]
theorem isSheaf_fppfTopology_over_of_zariski_subfunctors {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF_zariski : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    {I : Type u} (H : I → Subfunctor F)
    (hH_sheaf : ∀ i, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (H i).toFunctor)
    (hH_rep : ∀ i, AlgebraicSpace.representableByAlgebraicSpaces (H i).ι)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (Sigma.desc fun i ↦ (H i).ι)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F := sorry

end AlgebraicGeometry
