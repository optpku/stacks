module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ProperSmoothCurve.ConstantZMod
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Lemma 63.13.2: if `f : X ⟶ S` is a proper smooth morphism of schemes with
geometrically connected fibres of dimension `1` and `ℓ` is a prime number, then
each higher direct image of the constant sheaf of `ULift (ZMod ℓ)` is a
constructible abelian sheaf on the small étale site of `S`. -/
@[stacks 0GKV] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImage_constantZMod_isConstructible :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}],
    IsConstructibleEtale (fun {Y} g ↦ (etaleAbelianSheafPullback g).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G)
      (schemeHigherDirectImage f
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))) q))
