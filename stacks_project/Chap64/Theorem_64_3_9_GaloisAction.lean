module

public import Mathlib.FieldTheory.Galois.Notation
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap64.Lemma_64_3_2_Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Geometric

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

noncomputable section

/- Galois pullback on geometric étale cohomology. -/
#check (AlgebraicGeometry.SchemeOverField.galoisEtaleHq :
  ∀ {k : Type u} [Field k]
    [∀ Z : Scheme.{u},
      HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ)
    (σ : Gal(AlgebraicClosure k / k)),
    geometricEtaleHq X F j ⟶ geometricEtaleHq X F j)
