/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Relative finite-presentation approximation of morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S`, with quasi-compact
quasi-separated source and quasi-separated target, may be realized as a
directed inverse limit of algebraic spaces of finite presentation over the
target, with affine transition morphisms over the target.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed inverse system of algebraic spaces of finite presentation over a
fixed target, with affine transitions over that target, together with a limit
identification of a given morphism with the cone vertex over the target. -/
structure RelativeFinitePresentationApproximation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
  /-- The directed index type of the approximating inverse system. -/
  I : Type u
  /-- The preorder on the index type of the approximating inverse system. -/
  [preorderI : Preorder I]
  /-- The approximating inverse system has at least one stage. -/
  [nonemptyI : Nonempty I]
  /-- Any two stages of the approximating inverse system admit a common later stage. -/
  [directedI : IsDirected I (· ≤ ·)]
  /-- The inverse system of approximating algebraic spaces over `S`. -/
  D : OrderDual I ⥤ AlgebraicSpace S
  /-- The structure morphisms of the approximating stages over `Y`. -/
  σ : D ⟶ (Functor.const (OrderDual I)).obj Y
  /-- A cone from the approximating inverse system. -/
  c : Cone D
  /-- The cone is a limit cone. -/
  isLimit : IsLimit c
  /-- The identification of `X` with the vertex of the limit cone. -/
  iso : X ≅ c.pt
  /-- After identifying `X` with the cone vertex, the cone legs recover `f` over `Y`. -/
  over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f
  /-- Every transition morphism in the inverse system is affine. -/
  transitionAffine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))
  /-- Every approximating stage is of finite presentation over `Y`. -/
  stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)

namespace RelativeFinitePresentationApproximation

/-- Package a directed inverse system of algebraic spaces of finite presentation
over `Y`, with affine transitions and a limit identification recovering `f`. -/
def of {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (isLimit : IsLimit c) (iso : X ≅ c.pt)
    (over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
    (transitionAffine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h)))
    (stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)) :
    RelativeFinitePresentationApproximation f where
  I := I
  D := D
  σ := σ
  c := c
  isLimit := isLimit
  iso := iso
  over_lim := over_lim
  transitionAffine := transitionAffine
  stageFinitePresentation := stageFinitePresentation

/-- A relative finite-presentation approximation recovers `f` over `Y`, with
affine transitions and finite-presentation stages. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (A : RelativeFinitePresentationApproximation f) :
    -- Local instance justification (defeq pin): `A.D` and `homOfLE` are typed using the stored `A.preorderI`.
    letI := A.preorderI
    (∀ i, A.iso.hom ≫ A.c.π.app i ≫ A.σ.app i = f) ∧
    (∀ {i i' : A.I} (h : i ≤ i'), Affine (A.D.map (homOfLE h))) ∧
    ∀ i, FinitePresentation (A.σ.app i) :=
  sorry

end RelativeFinitePresentationApproximation

/-- A morphism of algebraic spaces over a scheme, with quasi-compact
quasi-separated source and quasi-separated target, admits a directed inverse
system of algebraic spaces of finite presentation over the target, with affine
transition morphisms, whose limit is identified with the source. -/
theorem exists_relativeFinitePresentationApproximation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiSeparated X] [IsQuasiSeparated Y] :
    Nonempty (RelativeFinitePresentationApproximation f) :=
  sorry

/-- Relative finite-presentation approximation of such a morphism is equivalent
to the existence of a directed inverse system with affine transitions,
finite-presentation stages over the target, and a limit identification of the
source recovering the morphism. -/
theorem exists_relativeFinitePresentationApproximation_nonempty_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiSeparated X] [IsQuasiSeparated Y] :
    Nonempty (RelativeFinitePresentationApproximation f) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace S)
        (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) (c : Cone D)
        (_ : IsLimit c) (iso : X ≅ c.pt)
        (_ : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))),
        ∀ i, FinitePresentation (σ.app i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
