/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A compatible morphism between chosen strict henselization schemes is unique. -/
theorem existsUnique_strictHenselizationComparison
    (S : Scheme.{u}) (sbar tbar : Scheme.GeometricPoint S)
    (RshS RshT : Type u)
    [CommRing RshS] [Algebra (S.presheaf.stalk sbar.image) RshS]
    [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]
    [CommRing RshT] [Algebra (S.presheaf.stalk tbar.image) RshT]
    [IsStrictHenselizationOf (S.presheaf.stalk tbar.image) RshT]
    (tbarToSsh : Spec (.of tbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (tbarToTsh : Spec (.of tbar.K) ⟶ strictHenselizationScheme S tbar RshT)
    (hS : tbarToSsh ≫ strictHenselizationMap S sbar RshS = tbar.hom)
    (hT : tbarToTsh ≫ strictHenselizationMap S tbar RshT = tbar.hom) :
    ∃! c : strictHenselizationScheme S tbar RshT ⟶
        strictHenselizationScheme S sbar RshS,
      c ≫ strictHenselizationMap S sbar RshS =
          strictHenselizationMap S tbar RshT ∧
        tbarToTsh ≫ c = tbarToSsh := sorry

/-- The canonical strict-henselization comparison is induced by retargeting pointed
étale neighborhoods along the given geometric point. -/
def StrictHenselization.comparison {S : Scheme.{u}} (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom) :
    strictHenselizationAt S t ⟶ strictHenselizationAt S s :=
  Spec.map (CommRingCat.ofHom (RingCat.Hom.hom
    (((StrictHenselianNeighborhood.canonical s).specializationPoint point point_over).presheafFiber.app
      (S.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat))))

/-- The canonical comparison of strict henselizations is a morphism over the base scheme. -/
theorem StrictHenselization.comparison_over {S : Scheme.{u}} (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom) :
    comparison s t point point_over ≫ toScheme S s = toScheme S t := sorry

/-- The canonical comparison sends the target's geometric closed point to the
specified geometric point of the source strict henselization. -/
theorem StrictHenselization.comparison_closedPoint {S : Scheme.{u}} (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom) :
    closedPoint t ≫ comparison s t point point_over = point := sorry

/-- The canonical comparison is the unique over-base morphism preserving the
specified geometric point. -/
theorem StrictHenselization.comparison_unique {S : Scheme.{u}} (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (other : strictHenselizationAt S t ⟶ strictHenselizationAt S s)
    (other_over : other ≫ toScheme S s = toScheme S t)
    (other_point : closedPoint t ≫ other = point) :
    other = comparison s t point point_over := sorry

end AlgebraicGeometry.Scheme

end
