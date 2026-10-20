/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Immersions of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is an immersion, closed immersion, or
open immersion when the corresponding transformation of functors of points is representable
and has the matching scheme morphism property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S}, (F ⟶ G) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S}, (F ⟶ G) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S}, (F ⟶ G) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isImmersion_iff :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G),
    IsImmersion f ↔
      (over (@AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})).presheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.spec :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G),
    IsImmersion f ↔
      yoneda.relativelyRepresentable f ∧
        ∀ ⦃U V : Over S⦄ (ξ : yoneda.obj U ⟶ G.functorOfPoints)
          (fst : yoneda.obj V ⟶ F.functorOfPoints) (snd : V ⟶ U),
          IsPullback fst (yoneda.map snd) f ξ → AlgebraicGeometry.IsImmersion snd.left)

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.id :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}, IsImmersion (𝟙 F))

#check (AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_iff :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G),
    IsClosedImmersion f ↔
      (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.spec :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G),
    IsClosedImmersion f ↔
      yoneda.relativelyRepresentable f ∧
        ∀ ⦃U V : Over S⦄ (ξ : yoneda.obj U ⟶ G.functorOfPoints)
          (fst : yoneda.obj V ⟶ F.functorOfPoints) (snd : V ⟶ U),
          IsPullback fst (yoneda.map snd) f ξ → AlgebraicGeometry.IsClosedImmersion snd.left)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.id :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}, IsClosedImmersion (𝟙 F))

#check (AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_iff :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G),
    IsOpenImmersion f ↔
      (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.spec :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G),
    IsOpenImmersion f ↔
      yoneda.relativelyRepresentable f ∧
        ∀ ⦃U V : Over S⦄ (ξ : yoneda.obj U ⟶ G.functorOfPoints)
          (fst : yoneda.obj V ⟶ F.functorOfPoints) (snd : V ⟶ U),
          IsPullback fst (yoneda.map snd) f ξ → AlgebraicGeometry.IsOpenImmersion snd.left)

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.id :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}, IsOpenImmersion (𝟙 F))

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.ofIsOpenImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} {f : F ⟶ G} [IsOpenImmersion f], IsImmersion f)

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.ofIsClosedImmersion :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} {f : F ⟶ G} [IsClosedImmersion f], IsImmersion f)

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.mono :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} {f : F ⟶ G} [IsImmersion f], Mono f)

#check (AlgebraicGeometry.AlgebraicSpace.over_presheaf_of_comp :
  ∀ {S : Scheme.{u}} {F G H : AlgebraicSpace S} {P : MorphismProperty Scheme.{u}}
    (f : F ⟶ G) (g : G ⟶ H) [Mono g],
    (over P).presheaf (f ≫ g) → (over P).presheaf f)

end AlgebraicGeometry.AlgebraicSpace
