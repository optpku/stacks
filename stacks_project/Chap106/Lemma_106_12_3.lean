/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_12_2_Invariant
public import stacks_project.Chap106.Definition_106_12_1_Moduli
public import stacks_project.Chap97.Theorem_97_17_2

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
    pullback (G.s.left ≫ φ) h ⟶ pullback φ h :=
  pullback.lift (pullback.fst (G.s.left ≫ φ) h ≫ G.s.left)
    (pullback.snd (G.s.left ≫ φ) h)
    ((Category.assoc (pullback.fst (G.s.left ≫ φ) h) G.s.left φ).trans
      pullback.condition)

/-- `baseChangeSrc φ h` projects to `U` as the source map of `G`. -/
theorem baseChangeSrc_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (h : Y' ⟶ Y) :
    G.baseChangeSrc φ h ≫ pullback.fst φ h =
      pullback.fst (G.s.left ≫ φ) h ≫ G.s.left :=
  sorry

/-- `baseChangeSrc φ h` projects to `Y'` as the second pullback projection. -/
theorem baseChangeSrc_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (h : Y' ⟶ Y) :
    G.baseChangeSrc φ h ≫ pullback.snd φ h =
      pullback.snd (G.s.left ≫ φ) h :=
  sorry

/-- The base-changed target map `R' ⟶ U'` of an invariant morphism `φ`, induced
by `G.t.left` on the same chosen `R' = Y' ×_Y R` as `baseChangeSrc`. -/
def baseChangeTgt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) (h : Y' ⟶ Y) :
    pullback (G.s.left ≫ φ) h ⟶ pullback φ h :=
  pullback.lift (pullback.fst (G.s.left ≫ φ) h ≫ G.t.left)
    (pullback.snd (G.s.left ≫ φ) h)
    ((Category.assoc (pullback.fst (G.s.left ≫ φ) h) G.t.left φ).trans
      ((congrArg (fun g ↦ pullback.fst (G.s.left ≫ φ) h ≫ g) hφ).trans
        pullback.condition))

/-- `baseChangeTgt φ hφ h` projects to `U` as the target map of `G`. -/
theorem baseChangeTgt_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) (h : Y' ⟶ Y) :
    G.baseChangeTgt φ hφ h ≫ pullback.fst φ h =
      pullback.fst (G.s.left ≫ φ) h ≫ G.t.left :=
  sorry

/-- `baseChangeTgt φ hφ h` projects to `Y'` as the second pullback projection. -/
theorem baseChangeTgt_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y Y' : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) (h : Y' ⟶ Y) :
    G.baseChangeTgt φ hφ h ≫ pullback.snd φ h =
      pullback.snd (G.s.left ≫ φ) h :=
  sorry

/-- Lemma 106.12.3 (1). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. A morphism `f : G.quotientStack ⟶ Y.toGroupoids` is a categorical
moduli space if and only if `G.atlasComp f` is an `R`-invariant categorical
quotient among morphisms of algebraic spaces over `S`. -/
@[stacks 0DUI]
theorem isCategoricalModuliSpace_iff_isCategoricalQuotient
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : G.quotientStack ⟶ Y.toGroupoids) :
    AlgebraicStack.IsCategoricalModuliSpace f ↔
      G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {W : AlgebraicSpace S} (ψ : G.U.left ⟶ W),
          G.IsInvariantHom ψ → ∃! χ : Y ⟶ W, G.atlasComp f ≫ χ = ψ :=
  sorry

/-- Lemma 106.12.3 (2). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. A morphism `f : G.quotientStack ⟶ Y.toGroupoids` is a uniform
categorical moduli space if and only if `G.atlasComp f` is a uniform
categorical quotient: after every flat base change `h : Y' ⟶ Y`, invariant
morphisms out of `Y' ×_Y U` factor uniquely through `Y' ×_Y U ⟶ Y'`. -/
@[stacks 0DUI]
theorem isUniformCategoricalModuliSpace_iff_isUniformCategoricalQuotient
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : G.quotientStack ⟶ Y.toGroupoids) :
    AlgebraicStack.IsUniformCategoricalModuliSpace f ↔
      G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) [AlgebraicSpace.Flat h]
          {W : AlgebraicSpace S} (ψ : pullback (G.atlasComp f) h ⟶ W)
          (hφ : G.IsInvariantHom (G.atlasComp f)),
          G.baseChangeTgt (G.atlasComp f) hφ h ≫ ψ =
              G.baseChangeSrc (G.atlasComp f) h ≫ ψ →
            ∃! χ : Y' ⟶ W, pullback.snd (G.atlasComp f) h ≫ χ = ψ :=
  sorry

/-- Lemma 106.12.3 (3). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, let `Y` be an algebraic
space, and let `C` be a full subcategory of algebraic spaces over `S`. A
morphism `f : G.quotientStack ⟶ Y.toGroupoids` is a categorical moduli space
in `C` if and only if `Y` lies in `C` and `G.atlasComp f` is an `R`-invariant
categorical quotient among morphisms in `C`. -/
@[stacks 0DUI]
theorem isCategoricalModuliSpaceIn_iff_isCategoricalQuotientIn
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : G.quotientStack ⟶ Y.toGroupoids)
    (C : ObjectProperty (AlgebraicSpace S)) :
    AlgebraicStack.IsCategoricalModuliSpaceIn C f ↔
      C Y ∧ G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {W : AlgebraicSpace S} (hW : C W) (ψ : G.U.left ⟶ W),
          G.IsInvariantHom ψ → ∃! χ : Y ⟶ W, G.atlasComp f ≫ χ = ψ :=
  sorry

/-- Lemma 106.12.3 (4). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, let `Y` be an algebraic
space, and let `C` be a full subcategory of algebraic spaces over `S`. A
morphism `f : G.quotientStack ⟶ Y.toGroupoids` is a uniform categorical moduli
space in `C` if and only if `Y` lies in `C` and `G.atlasComp f` is a uniform
categorical quotient in `C`. -/
@[stacks 0DUI]
theorem isUniformCategoricalModuliSpaceIn_iff_isUniformCategoricalQuotientIn
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : G.quotientStack ⟶ Y.toGroupoids)
    (C : ObjectProperty (AlgebraicSpace S)) :
    AlgebraicStack.IsUniformCategoricalModuliSpaceIn C f ↔
      C Y ∧ G.IsInvariantHom (G.atlasComp f) ∧
        ∀ {Y' : AlgebraicSpace S} (h : Y' ⟶ Y) (hY' : C Y')
          [AlgebraicSpace.Flat h] {W : AlgebraicSpace S} (hW : C W)
          (ψ : pullback (G.atlasComp f) h ⟶ W)
          (hφ : G.IsInvariantHom (G.atlasComp f)),
          G.baseChangeTgt (G.atlasComp f) hφ h ≫ ψ =
              G.baseChangeSrc (G.atlasComp f) h ≫ ψ →
            ∃! χ : Y' ⟶ W, pullback.snd (G.atlasComp f) h ≫ χ = ψ :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
