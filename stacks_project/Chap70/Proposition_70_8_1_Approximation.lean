module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Absolute Noetherian approximation of algebraic spaces

A quasi-compact quasi-separated algebraic space over `Spec ℤ` may be realized
as a directed inverse limit of quasi-separated algebraic spaces of finite type
over `ℤ` with affine transition morphisms.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The spectrum of the universe-`u` lift of `ℤ`. -/
abbrev specULiftInt : Scheme.{u} :=
  Spec (CommRingCat.of (ULift.{u} ℤ))

/-- A directed affine inverse system of quasi-separated finite-type algebraic
spaces over `ℤ`, together with a limit identification of a given algebraic
space with the cone vertex. -/
structure AbsoluteNoetherianApproximation (X : AlgebraicSpace specULiftInt) where
  /-- The directed index type of the approximating inverse system. -/
  I : Type u
  /-- The preorder on the index type of the approximating inverse system. -/
  [preorderI : Preorder I]
  /-- The approximating inverse system has at least one stage. -/
  [nonemptyI : Nonempty I]
  /-- Any two stages of the approximating inverse system admit a common later stage. -/
  [directedI : IsDirected I (· ≤ ·)]
  /-- The inverse system of approximating algebraic spaces over `Spec ℤ`. -/
  D : OrderDual I ⥤ AlgebraicSpace specULiftInt
  /-- A cone from the approximating inverse system. -/
  c : Cone D
  /-- The cone is a limit cone. -/
  isLimit : IsLimit c
  /-- The identification of `X` with the vertex of the limit cone. -/
  iso : X ≅ c.pt
  /-- Every transition morphism in the inverse system is affine. -/
  transitionAffine :
    ∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))
  /-- Every approximating stage is quasi-separated. -/
  stageQuasiSeparated :
    ∀ i : I, IsQuasiSeparated (D.obj (OrderDual.toDual i))
  /-- Every approximating stage is of finite type over `Spec ℤ`. -/
  stageFiniteType :
    ∀ i : I, FiniteType (toBase (D.obj (OrderDual.toDual i)))

namespace AbsoluteNoetherianApproximation

/-- Package a directed affine inverse system of quasi-separated finite-type
algebraic spaces over `ℤ`, together with a limit identification, as an absolute
Noetherian approximation. -/
def of (X : AlgebraicSpace specULiftInt)
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ AlgebraicSpace specULiftInt) (c : Cone D)
    (isLimit : IsLimit c) (iso : X ≅ c.pt)
    (transitionAffine :
      ∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii')))
    (stageQuasiSeparated :
      ∀ i : I, IsQuasiSeparated (D.obj (OrderDual.toDual i)))
    (stageFiniteType :
      ∀ i : I, FiniteType (toBase (D.obj (OrderDual.toDual i)))) :
    AbsoluteNoetherianApproximation X where
  I := I
  D := D
  c := c
  isLimit := isLimit
  iso := iso
  transitionAffine := transitionAffine
  stageQuasiSeparated := stageQuasiSeparated
  stageFiniteType := stageFiniteType

/-- An absolute Noetherian approximation identifies `X` with the vertex of its
limit cone. -/
theorem spec {X : AlgebraicSpace specULiftInt}
    (A : AbsoluteNoetherianApproximation X) :
    A.iso.hom ≫ A.iso.inv = 𝟙 X :=
  sorry

end AbsoluteNoetherianApproximation

/-- A quasi-compact quasi-separated algebraic space over `Spec ℤ` admits a
directed affine inverse system of quasi-separated finite-type algebraic spaces
over `ℤ` whose limit is isomorphic to it. -/
theorem exists_absoluteNoetherianApproximation
    (X : AlgebraicSpace specULiftInt) [IsQuasiCompact X] [IsQuasiSeparated X] :
    Nonempty (AbsoluteNoetherianApproximation X) :=
  sorry

/-- Absolute Noetherian approximation of a qcqs algebraic space over `Spec ℤ` is
equivalent to the existence of a directed inverse system with affine transitions,
quasi-separated finite-type stages over `ℤ`, and a limit identification. -/
theorem exists_absoluteNoetherianApproximation_nonempty_iff
    (X : AlgebraicSpace specULiftInt) [IsQuasiCompact X] [IsQuasiSeparated X] :
    Nonempty (AbsoluteNoetherianApproximation X) ↔
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ AlgebraicSpace specULiftInt) (c : Cone D)
        (_ : IsLimit c) (_ : X ≅ c.pt)
        (_ : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h)))
        (_ : ∀ i, IsQuasiSeparated (D.obj (OrderDual.toDual i))),
        ∀ i, FiniteType (toBase (D.obj (OrderDual.toDual i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
