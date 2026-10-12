/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Normal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A separated étale morphism over an integral normal scheme with separably closed function
field is an indexed coproduct of open immersions. -/
theorem separatedEtaleOpenDecomposition
    {X U : Scheme.{u}} [IsIntegral X] (hX : X.isNormal)
    [IsSepClosed X.functionField] (f : U ⟶ X) [Etale f] [IsSeparated f] :
    ∃ (ι : Type u) (V : ι → Scheme.{u}) (e : U ≅ ∐ V)
      (j : ∀ i, V i ⟶ X),
      (∀ i, IsOpenImmersion (j i)) ∧ e.hom ≫ Sigma.desc j = f := sorry

/-- An affine étale scheme over a closed subscheme of an affine integral normal scheme with
separably closed function field is a finite coproduct of open subschemes of that closed
subscheme. -/
theorem affineEtale_finiteOpenDecomposition
    {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X] (hX : X.isNormal)
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    [IsAffine V] (f : V ⟶ Z) [Etale f] :
    ∃ (n : ℕ) (W : Fin n → Scheme.{u}) (e : V ≅ ∐ W)
      (j : ∀ k, W k ⟶ Z),
      (∀ k, IsOpenImmersion (j k)) ∧ e.hom ≫ Sigma.desc j = f := sorry

/-- A surjective finite étale morphism with affine source over a closed subscheme of an
affine integral normal scheme with separably closed function field admits a section. -/
theorem surjectiveFiniteEtale_hasSection
    {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X] (hX : X.isNormal)
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    [IsAffine V] (f : V ⟶ Z) [Surjective f] [IsFinite f] [Etale f] :
    ∃ s : Z ⟶ V, s ≫ f = 𝟙 Z := sorry

end AlgebraicGeometry.Scheme.Hom
