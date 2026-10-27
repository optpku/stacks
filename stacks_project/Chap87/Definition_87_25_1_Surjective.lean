/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Surjective morphisms of formal algebraic spaces

A morphism of formal algebraic spaces is surjective when the induced map of
algebraic-space reductions is a surjective morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- The induced morphism of algebraic-space reductions along a morphism of
formal algebraic spaces, as the unique factor of `reductionι X ≫ f` through
`reductionι Y`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.mapReduction :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y),
    reduction X ⟶ reduction Y)

/- `mapReduction f` factors `reductionι X ≫ f` through `reductionι Y`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.mapReduction_spec :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y),
    NatTrans.vcomp (mapReduction f) (reductionι Y) =
      NatTrans.vcomp (reductionι X) f)

/- A morphism of reductions over `f` equals `mapReduction f`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.mapReduction_unique :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) {g : reduction X ⟶ reduction Y}
    (hg : NatTrans.vcomp g (reductionι Y) = NatTrans.vcomp (reductionι X) f),
    g = mapReduction f)

/- Reduction sends identity morphisms to identity morphisms. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.mapReduction_id :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [RX : Reduction X],
    mapReduction (𝟙 X) = 𝟙 (reduction X))

/- Reduction preserves composition. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.mapReduction_comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [RX : Reduction X] [RY : Reduction Y] [RZ : Reduction Z]
    (f : X ⟶ Y) (g : Y ⟶ Z),
    mapReduction (f ≫ g) = mapReduction f ≫ mapReduction g)

/- A morphism of formal algebraic spaces is surjective if the induced map of
underlying reduced algebraic spaces is surjective. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y),
    Prop)

/- The legacy surjectivity class is equivalent to the predicate on explicit reductions. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.surjective_iff_reductionData :
  ∀ {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y),
    Surjective f ↔ ReductionData.Surjective RX.toReductionData RY.toReductionData f)

/- On morphisms of algebraic spaces, viewed as formal algebraic spaces via
`instIsFormalAlgebraicSpace_functorOfPoints`, surjectivity agrees with
`AlgebraicSpace.Surjective`. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.surjective_functorOfPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints),
    Surjective f ↔ AlgebraicSpace.Surjective f)

namespace Surjective

/- The identity morphism of a formal algebraic space is surjective. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.id :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X],
    Surjective (𝟙 X))

/- An isomorphism of formal algebraic spaces is surjective. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [IsIso f],
    Surjective f)

/- A surjective morphism of algebraic spaces is surjective as a morphism of
formal algebraic spaces, via the functor-of-points reduction. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.ofAlgebraicSpace :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints)
    [AlgebraicSpace.Surjective f],
    Surjective f)

/- A surjective morphism of formal algebraic spaces induces a surjective
morphism of algebraic-space reductions. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.spec :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Surjective f],
    AlgebraicSpace.Surjective (mapReduction f))

/- A morphism of formal algebraic spaces is surjective as soon as the induced
map of algebraic-space reductions is surjective. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.of :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.Surjective (mapReduction f)),
    Surjective f)

end Surjective

end AlgebraicGeometry.FormalAlgebraicSpace
