module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.BaseChange

/-!
# Cartesian flat pullback compatibility

Canonical base-change properties and the existing cycle-level flat pullback
spelling for source-facing consumers.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeDimension.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} {r : ℕ}
    [LocallyOfFiniteType g],
    IsPullback f' g' g f → RelativeDimension g r → RelativeDimension g' r)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeDimension.pullback_fst :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {g : Z ⟶ Y} {r : ℕ}
    [LocallyOfFiniteType g], RelativeDimension g r →
    ∀ (f : X ⟶ Y) [HasPullback f g], RelativeDimension (pullback.fst f g) r)

#check (AlgebraicGeometry.AlgebraicSpace.relativeDimension_pullback_fst :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) (r : ℕ)
    [LocallyOfFiniteType g] [RelativeDimension g r] [HasPullback f g],
    RelativeDimension (pullback.fst f g) r)

#check (AlgebraicGeometry.AlgebraicSpace.Flat.pullback_fst :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {g : Z ⟶ Y}, Flat g →
    ∀ (f : X ⟶ Y) [HasPullback f g], Flat (pullback.fst f g))

#check (AlgebraicGeometry.AlgebraicSpace.flat_pullback_fst :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [Flat g] [HasPullback f g], Flat (pullback.fst f g))

public section

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Flat pullback of `k`-cycles along a morphism of relative dimension `r`, as
an additive map `Z_k(Y) →+ Z_{k + r}(X)`. This is definitionally
`flatPullbackHom`. -/
noncomputable def cycleFlatPullback {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    (cycleGroup pY) δ k →+ (cycleGroup pX) δ (k + (r : ℤ)) :=
  flatPullbackHom pY pX δ f r hf k

/-- Canonical flat pullback of the zero cycle is zero. -/
theorem cycleFlatPullback_zero {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    cycleFlatPullback pY pX δ f r hf k 0 = 0 :=
  (cycleFlatPullback pY pX δ f r hf k).map_zero


end AlgebraicGeometry.AlgebraicSpace.Hom
