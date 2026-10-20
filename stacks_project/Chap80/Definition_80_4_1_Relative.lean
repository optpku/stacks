/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.pullbackSpace :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a →
        ∀ {U : Over S} (ξ : yoneda.obj U ⟶ G), AlgebraicGeometry.AlgebraicSpace S)
#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.pullbackSpace_functorOfPoints :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      (ha : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a) →
        ∀ {U : Over S} (ξ : yoneda.obj U ⟶ G),
          (ha.pullbackSpace ξ).functorOfPoints = pullback ξ a)
#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      (ha : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a) →
        ∀ {U : Over S} (ξ : yoneda.obj U ⟶ G),
          ha.pullbackSpace ξ ⟶ AlgebraicGeometry.AlgebraicSpace.ofOver U)
#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom_fst :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      (ha : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a) →
        ∀ {U : Over S} (ξ : yoneda.obj U ⟶ G),
          ha.pullbackHom ξ = pullback.fst ξ a)
#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.has :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a →
        MorphismProperty (AlgebraicGeometry.AlgebraicSpace S) → Prop)
#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.has_iff :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      (ha : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a) →
        ∀ (P : MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)),
          ha.has P ↔
            ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ))
#check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces :
    ∀ {S : Scheme.{u}},
      MorphismProperty (AlgebraicGeometry.AlgebraicSpace S) →
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))
#check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces_iff :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      ∀ (P : MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)),
        AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces P a ↔
          AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a ∧
            ∀ (ha : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a)
              ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ))
#check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces.of :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G},
      ∀ (P : MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)),
        (ha : AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a) →
          (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ)) →
            AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces P a)
#check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces.representable :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
      {P : MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)},
      AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces P a →
        AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a)
#check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces.property_pullbackHom :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
      {P : MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)},
      (h : AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces P a) →
        ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P ((h.representable).pullbackHom ξ))
