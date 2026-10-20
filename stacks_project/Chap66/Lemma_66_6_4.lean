/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Separation.EtaleFromScheme
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 66.6.4: let `S` be a scheme, `X` an algebraic space over `S`, and `U` a
separated scheme. If `φ : U ⟶ X` is étale, then `φ` is separated, and the represented
kernel pair `R = U ×_X U` is a separated scheme. -/
@[stacks 03FZ] #check (AlgebraicGeometry.AlgebraicSpace.isSeparated_of_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [Scheme.IsSeparated U.left] (φ : AlgebraicSpace.ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ),
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
      MorphismProperty Scheme.{u})).presheaf φ)

#check (AlgebraicGeometry.AlgebraicSpace.isSeparated_kernelPair :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [Scheme.IsSeparated U.left] (φ : AlgebraicSpace.ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ),
    Scheme.IsSeparated (AlgebraicSpace.kernelPair φ hφ.rep).left.left)
