module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a proper smooth morphism of schemes with geometrically connected fibres of
dimension `1` and a prime `ℓ`, every higher direct image of the constant abelian
sheaf of `ULift (ZMod ℓ)` is constructible on the small étale site of the base. -/
@[stacks 0GKV]
theorem higherDirectImage_constantZMod_isConstructible
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}] :
    IsConstructibleEtale (fun {Y} g ↦ (etaleAbelianSheafPullback g).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G)
      (schemeHigherDirectImage f
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))) q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
