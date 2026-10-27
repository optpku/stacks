/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallInvariant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Moduli

/-!
# Categorical moduli spaces versus categorical quotients

For a flat, locally finitely presented groupoid in algebraic spaces, a morphism
out of the quotient stack is a (uniform) categorical moduli space if and only if
the associated atlas composite is a (uniform) categorical quotient. The same
comparison holds in a full subcategory of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The base-changed source map `R' ⟶ U'` of a morphism `φ : U ⟶ Y`, induced
by `G.s.left` on `R' = Y' ×_Y R` and `U' = Y' ×_Y U`. -/
def baseChangeSrc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (h : Y' ⟶ Y) :
    CategoryTheory.Limits.pullback (G.s.left ≫ φ) h ⟶ CategoryTheory.Limits.pullback φ h :=
  CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst (G.s.left ≫ φ) h ≫ G.s.left)
    (CategoryTheory.Limits.pullback.snd (G.s.left ≫ φ) h)
    ((Category.assoc (CategoryTheory.Limits.pullback.fst (G.s.left ≫ φ) h) G.s.left φ).trans
      CategoryTheory.Limits.pullback.condition)

/-- `baseChangeSrc φ h` projects to `U` as the source map of `G`. -/
theorem baseChangeSrc_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (h : Y' ⟶ Y) :
    G.baseChangeSrc φ h ≫ CategoryTheory.Limits.pullback.fst φ h =
      CategoryTheory.Limits.pullback.fst (G.s.left ≫ φ) h ≫ G.s.left := sorry

/-- `baseChangeSrc φ h` projects to `Y'` as the second pullback projection. -/
theorem baseChangeSrc_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (h : Y' ⟶ Y) :
    G.baseChangeSrc φ h ≫ CategoryTheory.Limits.pullback.snd φ h =
      CategoryTheory.Limits.pullback.snd (G.s.left ≫ φ) h := sorry

/-- The base-changed target map `R' ⟶ U'` of an invariant morphism `φ`, induced
by `G.t.left` on the same chosen `R' = Y' ×_Y R` as `baseChangeSrc`. -/
def baseChangeTgt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) (h : Y' ⟶ Y) :
    CategoryTheory.Limits.pullback (G.s.left ≫ φ) h ⟶ CategoryTheory.Limits.pullback φ h :=
  CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst (G.s.left ≫ φ) h ≫ G.t.left)
    (CategoryTheory.Limits.pullback.snd (G.s.left ≫ φ) h)
    ((Category.assoc (CategoryTheory.Limits.pullback.fst (G.s.left ≫ φ) h) G.t.left φ).trans
      ((congrArg (fun g ↦ CategoryTheory.Limits.pullback.fst (G.s.left ≫ φ) h ≫ g) hφ).trans
        CategoryTheory.Limits.pullback.condition))

/-- `baseChangeTgt φ hφ h` projects to `U` as the target map of `G`. -/
theorem baseChangeTgt_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) (h : Y' ⟶ Y) :
    G.baseChangeTgt φ hφ h ≫ CategoryTheory.Limits.pullback.fst φ h =
      CategoryTheory.Limits.pullback.fst (G.s.left ≫ φ) h ≫ G.t.left := sorry

/-- `baseChangeTgt φ hφ h` projects to `Y'` as the second pullback projection. -/
theorem baseChangeTgt_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) (h : Y' ⟶ Y) :
    G.baseChangeTgt φ hφ h ≫ CategoryTheory.Limits.pullback.snd φ h =
      CategoryTheory.Limits.pullback.snd (G.s.left ≫ φ) h := sorry

/-- Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. A morphism `f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids` is a categorical
moduli space if and only if `G.atlasComp f` is an `R`-invariant categorical
quotient among morphisms of algebraic spaces over `S`. -/
theorem isCategoricalModuliSpace_iff_isCategoricalQuotient
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids) :
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsCategoricalModuliSpace f ↔
      G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {W : AlgebraicSpace S} (ψ : G.U.left ⟶ W),
          G.IsInvariantHom ψ → ∃! χ : Y ⟶ W, G.atlasComp f ≫ χ = ψ := sorry

/-- Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. A morphism `f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids` is a uniform
categorical moduli space if and only if `G.atlasComp f` is a uniform
categorical quotient: after every flat base change `h : Y' ⟶ Y`, invariant
morphisms out of `Y' ×_Y U` factor uniquely through `Y' ×_Y U ⟶ Y'`. -/
theorem isUniformCategoricalModuliSpace_iff_isUniformCategoricalQuotient
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids) :
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsUniformCategoricalModuliSpace f ↔
      G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) [AlgebraicSpace.Flat h]
          {W : AlgebraicSpace S} (ψ : CategoryTheory.Limits.pullback (G.atlasComp f) h ⟶ W)
          (hφ : G.IsInvariantHom (G.atlasComp f)),
          G.baseChangeTgt (G.atlasComp f) hφ h ≫ ψ =
              G.baseChangeSrc (G.atlasComp f) h ≫ ψ →
            ∃! χ : Y' ⟶ W, CategoryTheory.Limits.pullback.snd (G.atlasComp f) h ≫ χ = ψ := sorry

/-- Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, let `Y` be an algebraic
space, and let `C` be a full subcategory of algebraic spaces over `S`. A
morphism `f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids` is a categorical moduli space
in `C` if and only if `Y` lies in `C` and `G.atlasComp f` is an `R`-invariant
categorical quotient among morphisms in `C`. -/
theorem isCategoricalModuliSpaceIn_iff_isCategoricalQuotientIn
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids)
    (C : ObjectProperty (AlgebraicSpace S)) :
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsCategoricalModuliSpaceIn C f ↔
      C Y ∧ G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {W : AlgebraicSpace S} (hW : C W) (ψ : G.U.left ⟶ W),
          G.IsInvariantHom ψ → ∃! χ : Y ⟶ W, G.atlasComp f ≫ χ = ψ := sorry

/-- Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, let `Y` be an algebraic
space, and let `C` be a full subcategory of algebraic spaces over `S`. A
morphism `f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids` is a uniform categorical moduli
space in `C` if and only if `Y` lies in `C` and `G.atlasComp f` is a uniform
categorical quotient in `C`. -/
theorem isUniformCategoricalModuliSpaceIn_iff_isUniformCategoricalQuotientIn
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids)
    (C : ObjectProperty (AlgebraicSpace S)) :
    -- Local instance justification (defeq pin): the algebraic-stack moduli predicate is indexed by the proved algebraicity of this concrete quotient; the explicit groupoid cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack G) :=
      isAlgebraicStack_quotientStack_of_flat G inferInstance inferInstance
    AlgebraicStack.IsUniformCategoricalModuliSpaceIn C f ↔
      C Y ∧ G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) (hY' : C Y')
          [AlgebraicSpace.Flat h] {W : AlgebraicSpace S} (hW : C W)
          (ψ : CategoryTheory.Limits.pullback (G.atlasComp f) h ⟶ W)
          (hφ : G.IsInvariantHom (G.atlasComp f)),
          G.baseChangeTgt (G.atlasComp f) hφ h ≫ ψ =
              G.baseChangeSrc (G.atlasComp f) h ≫ ψ →
            ∃! χ : Y' ⟶ W, CategoryTheory.Limits.pullback.snd (G.atlasComp f) h ≫ χ = ψ := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
