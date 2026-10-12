/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap87.Lemma_87_34_3_Reduction

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

/-- The induced morphism of algebraic-space reductions along a morphism of
formal algebraic spaces, as the unique factor of `reductionι X ≫ f` through
`reductionι Y`. -/
def mapReduction {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [RX : Reduction X] [RY : Reduction Y] (f : X ⟶ Y) :
    reduction X ⟶ reduction Y :=
  Classical.choose (RY.liftUnique RX.isReduced (reductionι X ≫ f))

/-- `mapReduction f` factors `reductionι X ≫ f` through `reductionι Y`. -/
theorem mapReduction_spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) :
    NatTrans.vcomp (mapReduction f) (reductionι Y) =
      NatTrans.vcomp (reductionι X) f :=
  sorry

/-- A morphism of reductions over `f` equals `mapReduction f`. -/
theorem mapReduction_unique {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) {g : reduction X ⟶ reduction Y}
    (hg : NatTrans.vcomp g (reductionι Y) = NatTrans.vcomp (reductionι X) f) :
    g = mapReduction f :=
  sorry

/-- Reduction sends identity morphisms to identity morphisms. -/
theorem mapReduction_id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] :
    mapReduction (𝟙 X) = 𝟙 (reduction X) :=
  sorry

/-- Reduction preserves composition. -/
theorem mapReduction_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [Reduction X] [Reduction Y] [Reduction Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapReduction (f ≫ g) = mapReduction f ≫ mapReduction g :=
  sorry

/-- A morphism of formal algebraic spaces is surjective if the induced map of
underlying reduced algebraic spaces is surjective. -/
@[mk_iff]
class Surjective {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) : Prop where
  /-- The induced map of reductions is a surjective morphism of algebraic
  spaces. -/
  map_surjective : AlgebraicSpace.Surjective (mapReduction f)

namespace Surjective

/-- The identity morphism of a formal algebraic space is surjective. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] : Surjective (𝟙 X) :=
  sorry

/-- An isomorphism of formal algebraic spaces is surjective. -/
instance of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [IsIso f] : Surjective f :=
  sorry

/-- A surjective morphism of algebraic spaces is surjective as a morphism of
formal algebraic spaces, via the functor-of-points reduction. -/
instance ofAlgebraicSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints)
    [AlgebraicSpace.Surjective f] : Surjective f :=
  sorry

/-- A surjective morphism of formal algebraic spaces induces a surjective
morphism of algebraic-space reductions. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y) [Surjective f] :
    AlgebraicSpace.Surjective (mapReduction f) :=
  sorry

/-- A morphism of formal algebraic spaces is surjective as soon as the induced
map of algebraic-space reductions is surjective. -/
theorem of {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.Surjective (mapReduction f)) : Surjective f :=
  sorry

end Surjective

/-- On morphisms of algebraic spaces, viewed as formal algebraic spaces via
`instIsFormalAlgebraicSpace_functorOfPoints`, surjectivity agrees with
`AlgebraicSpace.Surjective`. -/
theorem surjective_functorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    Surjective f ↔ AlgebraicSpace.Surjective f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
