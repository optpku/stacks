/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.EtaleImage
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.10 (1): let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`U` be a scheme and let `f : U ⟶ X` be an étale morphism. Let `X' ⊂ X` be the open
subspace corresponding to the open `|f|(|U|) ⊂ |X|` via Lemma 66.4.8. Then `f` factors
through a surjective étale morphism `f' : U ⟶ X'`. -/
@[stacks 06NF] #check
  (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.exists_surjective_etale_lift :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} {f : ofOver U ⟶ X}
      (hf : (MorphismProperty.over (@Etale)).presheaf f)
      (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f)),
      ∃ f' : ofOver U ⟶ X'.X, f' ≫ X'.ι = f ∧
        (MorphismProperty.over (@Etale)).presheaf f' ∧
          (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f')

/- Lemma 66.4.10 (2): moreover, if `R = U ×_X U`, then `R = U ×_{X'} U`. -/
@[stacks 06NF] #check
  (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.isKernelPair_etale_lift :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} {f : ofOver U ⟶ X}
      (hf : (MorphismProperty.over (@Etale)).presheaf f)
      (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
      {f' : yoneda.obj U ⟶ X'.X.functorOfPoints} (hfac : f' ≫ X'.ι = f),
      IsKernelPair f' (yoneda.map (kernelPair f hf.rep).t)
        (yoneda.map (kernelPair f hf.rep).s))

/- Lemma 66.4.10 (3): moreover, if `R = U ×_X U`, then `X'` has the presentation
`X' = U/R`. -/
@[stacks 06NF] #check
  (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.presentation_spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} {f : ofOver U ⟶ X}
      (hf : (MorphismProperty.over (@Etale)).presheaf f)
      (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
      {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f),
      (OpenSubspace.presentation hf X' hX' hfac).U = U ∧
        (OpenSubspace.presentation hf X' hX' hfac).R = kernelPair f hf.rep ∧
          (OpenSubspace.presentation hf X' hX' hfac).atlas = f')
