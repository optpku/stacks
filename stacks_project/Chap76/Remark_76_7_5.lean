/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Descent

/-!
# Alternative constructions of the sheaf of differentials

Three étale descent presentations recover the canonical relative differential sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials
open AlgebraicGeometry.AlgebraicSpace.QCoh

universe u

/- Remark 76.7.5. Relative differentials can be constructed by étale glueing. -/
@[stacks 04CW] #check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.glued_isIsomorphic_relativeDifferentials :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U Y : Over S} (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X)
    [Etale φ] [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ],
    IsIsomorphic ((inclusion X).obj (glued f φ)) (relativeDifferentials f))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.cokerGlued_isIsomorphic_relativeDifferentials :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U : Over S} (f : X ⟶ Y) (φ : ofOver U ⟶ X)
    [Etale φ] [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ],
    IsIsomorphic ((inclusion X).obj (cokerGlued f φ)) (relativeDifferentials f))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.diagramGlued_isIsomorphic_relativeDifferentials :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U V : Over S} (f : X ⟶ Y) (ψ : U ⟶ V)
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) [Etale a] [Etale b]
    (sq : CommSq a (ofOverMap ψ) f b)
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a],
    IsIsomorphic ((inclusion X).obj (diagramGlued f ψ a b sq)) (relativeDifferentials f))

