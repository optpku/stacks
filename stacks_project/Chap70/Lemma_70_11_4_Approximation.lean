module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Closed-immersion approximation of algebraic spaces

A closed immersion of algebraic spaces over a scheme `S`, with quasi-compact
quasi-separated target, may be realized as a directed inverse limit of closed
immersions of finite presentation into that target, with closed-immersion
transition morphisms.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed inverse system of closed immersions of finite presentation into a
fixed target, with closed-immersion transitions, together with a limit
identification of a given closed immersion with the cone vertex over the
target. -/
structure ClosedImmersionApproximation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsClosedImmersion f] where
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
  /-- Every transition morphism in the inverse system is a closed immersion. -/
  transitionClosedImmersion :
    ∀ {i i' : I} (h : i ≤ i'), IsClosedImmersion (D.map (homOfLE h))
  /-- Every approximating stage is a closed immersion into `Y`. -/
  stageClosedImmersion : ∀ i, IsClosedImmersion (σ.app i)
  /-- Every approximating stage is of finite presentation over `Y`. -/
  stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)

namespace ClosedImmersionApproximation

/-- Package a directed inverse system of closed immersions of finite presentation
into `Y`, with closed-immersion transitions and a limit identification recovering
`f`. -/
def of {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (isLimit : IsLimit c) (iso : X ≅ c.pt)
    (over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
    (transitionClosedImmersion :
      ∀ {i i' : I} (h : i ≤ i'), IsClosedImmersion (D.map (homOfLE h)))
    (stageClosedImmersion : ∀ i, IsClosedImmersion (σ.app i))
    (stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)) :
    ClosedImmersionApproximation f where
  I := I
  D := D
  σ := σ
  c := c
  isLimit := isLimit
  iso := iso
  over_lim := over_lim
  transitionClosedImmersion := transitionClosedImmersion
  stageClosedImmersion := stageClosedImmersion
  stageFinitePresentation := stageFinitePresentation

/-- A closed-immersion approximation recovers `f` over `Y`, with closed-immersion
transitions and closed immersions of finite presentation as stages. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsClosedImmersion f] (A : ClosedImmersionApproximation f) :
    -- Local instance justification (defeq pin): `A.D` and `homOfLE` are typed using the stored `A.preorderI`.
    letI := A.preorderI
    (∀ i, A.iso.hom ≫ A.c.π.app i ≫ A.σ.app i = f) ∧
      (∀ {i i' : A.I} (h : i ≤ i'), IsClosedImmersion (A.D.map (homOfLE h))) ∧
      (∀ i, IsClosedImmersion (A.σ.app i)) ∧
      ∀ i, FinitePresentation (A.σ.app i) :=
  sorry

end ClosedImmersionApproximation

/-- A closed immersion of algebraic spaces over a scheme, with quasi-compact
quasi-separated target, admits a directed inverse system of closed immersions of
finite presentation into the target, with closed-immersion transitions, whose
limit is identified with the source. -/
theorem exists_closedImmersionApproximation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsClosedImmersion f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    Nonempty (ClosedImmersionApproximation f) :=
  sorry

/-- Closed-immersion approximation of such a morphism is equivalent to the
existence of a directed inverse system with closed-immersion transitions,
closed immersions of finite presentation as stages over the target, and a limit
identification of the source recovering the morphism. -/
theorem exists_closedImmersionApproximation_nonempty_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsClosedImmersion f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    Nonempty (ClosedImmersionApproximation f) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace S)
        (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) (c : Cone D)
        (_ : IsLimit c) (iso : X ≅ c.pt)
        (_ : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
        (_ : ∀ {i i' : I} (h : i ≤ i'), IsClosedImmersion (D.map (homOfLE h)))
        (_ : ∀ i, IsClosedImmersion (σ.app i)),
        ∀ i, FinitePresentation (σ.app i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
