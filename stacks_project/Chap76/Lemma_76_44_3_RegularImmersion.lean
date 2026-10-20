/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Implications
public import stacks_project.Chap65.Lemma_65_12_4_Immersion

/-!
# Regular immersions of algebraic spaces

A representable morphism of algebraic spaces over a scheme `S` is a
Koszul-regular, `H₁`-regular, or quasi-regular immersion when every étale
scheme pullback has the corresponding regularity. The canonical regularity
classes and their identity instances are available together with immersion
inference.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S}, (Z ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S}, (Z ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S}, (Z ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, IsKoszulRegularImmersion (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, IsH1RegularImmersion (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, IsQuasiRegularImmersion (𝟙 X))

end AlgebraicGeometry.AlgebraicSpace
