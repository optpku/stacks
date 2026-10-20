module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_13_2_InverseImage

/-!
# Elementary distinguished squares of algebraic spaces

A pair `(j : U ⟶ W, f : V ⟶ W)` is an elementary distinguished square when `j` is
an open immersion, `f` is étale, and the canonical morphism from the inverse image of
the reduced complement `T = W \ U` to `T` is an isomorphism.
-/

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare :
  ∀ {S : Scheme.{u}} {U V W : AlgebraicGeometry.AlgebraicSpace S},
    (U ⟶ W) → (V ⟶ W) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.reducedComplement :
  ∀ {S : Scheme.{u}} {W : AlgebraicGeometry.AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.OpenSubspace W →
      AlgebraicGeometry.AlgebraicSpace.ClosedSubspace W)
