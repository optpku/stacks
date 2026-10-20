module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Affine approximation of algebraic spaces

An affine morphism of algebraic spaces over a scheme `S`, with quasi-compact
quasi-separated target, may be realized as a directed inverse limit of affine
morphisms of finite presentation over that target, with affine transition
morphisms.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed inverse system of affine morphisms of finite presentation over a
fixed target, with affine transitions, together with a limit identification of a
given affine morphism with the cone vertex over the target. -/
structure AffineApproximation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Affine f] where
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
  /-- Every approximating stage is affine over `Y`. -/
  stageAffine : ∀ i, Affine (σ.app i)
  /-- Every approximating stage is of finite presentation over `Y`. -/
  stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)

namespace AffineApproximation

/-- Package a directed inverse system of affine morphisms of finite presentation
over `Y`, with affine transitions and a limit identification recovering `f`. -/
def of {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (isLimit : IsLimit c) (iso : X ≅ c.pt)
    (over_lim : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
    (transitionAffine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h)))
    (stageAffine : ∀ i, Affine (σ.app i))
    (stageFinitePresentation : ∀ i, FinitePresentation (σ.app i)) :
    AffineApproximation f where
  I := I
  D := D
  σ := σ
  c := c
  isLimit := isLimit
  iso := iso
  over_lim := over_lim
  transitionAffine := transitionAffine
  stageAffine := stageAffine
  stageFinitePresentation := stageFinitePresentation

/-- An affine approximation recovers `f` over `Y`, with affine transitions and
affine morphisms of finite presentation as stages. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Affine f] (A : AffineApproximation f) :
    -- Local instance justification (defeq pin): `A.D` and `homOfLE` are typed using the stored `A.preorderI`.
    letI := A.preorderI
    (∀ i, A.iso.hom ≫ A.c.π.app i ≫ A.σ.app i = f) ∧
      (∀ {i i' : A.I} (h : i ≤ i'), Affine (A.D.map (homOfLE h))) ∧
      (∀ i, Affine (A.σ.app i)) ∧
      ∀ i, FinitePresentation (A.σ.app i) :=
  sorry

end AffineApproximation

/-- An affine morphism of algebraic spaces over a scheme, with quasi-compact
quasi-separated target, admits a directed inverse system of affine morphisms of
finite presentation over the target, with affine transitions, whose limit is
identified with the source. -/
theorem exists_affineApproximation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Affine f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    Nonempty (AffineApproximation f) :=
  sorry

/-- Affine approximation of such a morphism is equivalent to the existence of a
directed inverse system with affine transitions, affine morphisms of finite
presentation as stages over the target, and a limit identification of the source
recovering the morphism. -/
theorem exists_affineApproximation_nonempty_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Affine f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    Nonempty (AffineApproximation f) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace S)
        (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) (c : Cone D)
        (_ : IsLimit c) (iso : X ≅ c.pt)
        (_ : ∀ i, iso.hom ≫ c.π.app i ≫ σ.app i = f)
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h)))
        (_ : ∀ i, Affine (σ.app i)),
        ∀ i, FinitePresentation (σ.app i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
