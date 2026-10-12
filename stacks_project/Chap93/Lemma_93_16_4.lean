/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import stacks_project.Chap90.Definition_90_9_1_Smooth
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation

/-!
# Unobstructed deformation category of a curve with isolated lci singularities

If `X` is a separated finite-type scheme over `k` of dimension at most one,
a local complete intersection over `k`, and smooth over `k` except at finitely
many points, then the deformation category `Def_X` of Example 93.9.1 is
unobstructed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]

/-- The slice projection `p_{x0} : Def_X ⥤ C_Λ` of Example 93.9.1. -/
abbrev deformationForget : deformationCategory Λ k X hX ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k

/-- The slice projection of `Def_X` evaluates an object `(A, Y) → (k, X)` to `A`. -/
theorem deformationForget_obj (x : deformationCategory Λ k X hX) :
    (deformationForget Λ k X hX).obj x = x.left.base := sorry

/-- The slice projection `p_{x0} : Def_X ⥤ C_Λ` is cofibered in groupoids. -/
instance instInGroupoids_deformationForget :
    IsFibered.InGroupoids (deformationForget Λ k X hX).op := sorry

/-- Lemma 93.16.4: in Example 93.9.1, if a scheme `X` over `k` is separated and of
finite type, `topologicalKrullDim X ≤ 1`, a local complete intersection over `k`
via `Syntomic hX`, and `X ⟶ Spec(k)` is smooth except at finitely many points,
then `Def_X` is unobstructed. -/
@[stacks 0DZQ]
theorem isUnobstructed_deformationCategory
    [Scheme.Hom.FiniteType hX] [IsSeparated hX] [Syntomic hX]
    (hdim : topologicalKrullDim X ≤ 1)
    (hns : {x : X | ¬ Scheme.Hom.SmoothAt hX x}.Finite) :
    Functor.IsUnobstructed (deformationForget Λ k X hX) := sorry

/-- Infinitesimal lifting along surjections in `C_Λ` for objects of `Def_X` when
`X` is separated of finite type, of dimension at most one, a local complete
intersection over `k`, and smooth except at finitely many points. -/
theorem deformationCategory_exists_lift
    [Scheme.Hom.FiniteType hX] [IsSeparated hX] [Syntomic hX]
    (hdim : topologicalKrullDim X ≤ 1)
    (hns : {x : X | ¬ Scheme.Hom.SmoothAt hX x}.Finite)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y : ArtinianLocalAlgCat Λ k} {x : deformationCategory Λ k X hX}
    (α : y ⟶ (deformationForget Λ k X hX).obj x)
    (hα : (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift f α) :
    ∃ (x' : deformationCategory Λ k X hX) (β : x' ⟶ x)
      (γ : (deformationForget Λ k X hX).obj x' ⟶ y),
      (deformationForget Λ k X hX).IsHomLift f β ∧
        (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift (𝟙 B) γ ∧
        γ ≫ α = (deformationForget Λ k X hX).map β := sorry

end FlatSchemeCat

