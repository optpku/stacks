module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_71_1_Constructible
public import stacks_project.Chap59.Lemma_59_51_7_HigherDirectImage
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import stacks_project.Chap59.Proposition_59_54_2_Leray_spectral_sequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 63.13.2: if `f : X ⟶ S` is a proper smooth morphism of schemes with
geometrically connected fibres of dimension `1` and `ℓ` is a prime number, then
each higher direct image of the constant sheaf of `ULift (ZMod ℓ)` is a
constructible abelian sheaf on the small étale site of `S`. -/
@[stacks 0GKV]
theorem higherDirectImage_constantZMod_isConstructible
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}] :
    IsConstructibleEtale (fun {Y} g ↦ (etaleAbelianSheafPullback g).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G)
      (etaleHigherDirectImage f
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))) q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
