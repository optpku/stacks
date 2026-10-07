module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Lemma_101_6_6_Comparison
public import stacks_project.Chap101.Lemma_101_6_6_Isom

/-!
# Fibre-product and Isom comparisons for separation axioms

If `f : X ⟶ Y` is a separated (resp. quasi-separated, resp. quasi-DM, resp.
DM) morphism of algebraic stacks, then `T1 ×_X T2 ⟶ T1 ×_Y T2` and
`Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` are proper (resp. quasi-compact
and quasi-separated, resp. locally quasi-finite, resp. unramified).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.6.6 (1): if `f` is a separated morphism of algebraic stacks, then
the comparison `T1 ×_X T2 ⟶ T1 ×_Y T2` is proper. -/
@[stacks 0CPL]
theorem fibreProductComparison_proper {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f]
    {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (fibreProductComparison f x1 x2) :=
  sorry

/-- Lemma 101.6.6 (2): if `f` is a quasi-separated morphism of algebraic stacks,
then the comparison `T1 ×_X T2 ⟶ T1 ×_Y T2` is quasi-compact and
quasi-separated. -/
@[stacks 0CPL]
theorem fibreProductComparison_quasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (fibreProductComparison f x1 x2) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (fibreProductComparison f x1 x2) :=
  sorry

/-- The comparison `T1 ×_X T2 ⟶ T1 ×_Y T2` along a quasi-separated morphism is
quasi-compact. -/
theorem fibreProductComparison_quasiCompact {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
      (fibreProductComparison f x1 x2) :=
  sorry

/-- The comparison `T1 ×_X T2 ⟶ T1 ×_Y T2` along a quasi-separated morphism is
quasi-separated. -/
theorem fibreProductComparison_isQuasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (fibreProductComparison f x1 x2) :=
  sorry

/-- Lemma 101.6.6 (3): if `f` is a quasi-DM morphism of algebraic stacks, then
the comparison `T1 ×_X T2 ⟶ T1 ×_Y T2` is locally quasi-finite. -/
@[stacks 0CPL]
theorem fibreProductComparison_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiDM f] {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (fibreProductComparison f x1 x2) :=
  sorry

/-- Lemma 101.6.6 (4): if `f` is a DM morphism of algebraic stacks, then the
comparison `T1 ×_X T2 ⟶ T1 ×_Y T2` is unramified. -/
@[stacks 0CPL]
theorem fibreProductComparison_unramified {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [DM f] {T1 T2 : AlgebraicSpace S} (x1 : T1.toGroupoids ⟶ X)
    (x2 : T2.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (fibreProductComparison f x1 x2) :=
  sorry

/-- Lemma 101.6.6 (5): if `f` is a separated morphism of algebraic stacks, then
`Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is proper. -/
@[stacks 0CPL]
theorem isomComparison_proper {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (isomComparison f x1 x2) :=
  sorry

/-- Lemma 101.6.6 (6): if `f` is a quasi-separated morphism of algebraic stacks,
then `Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is quasi-compact and
quasi-separated. -/
@[stacks 0CPL]
theorem isomComparison_quasiSeparated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (isomComparison f x1 x2) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (isomComparison f x1 x2) :=
  sorry

/-- The Isom comparison along a quasi-separated morphism is quasi-compact. -/
theorem isomComparison_quasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
      (isomComparison f x1 x2) :=
  sorry

/-- The Isom comparison along a quasi-separated morphism is quasi-separated. -/
theorem isomComparison_isQuasiSeparated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (isomComparison f x1 x2) :=
  sorry

/-- Lemma 101.6.6 (7): if `f` is a quasi-DM morphism of algebraic stacks, then
`Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is locally quasi-finite. -/
@[stacks 0CPL]
theorem isomComparison_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiDM f] {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (isomComparison f x1 x2) :=
  sorry

/-- Lemma 101.6.6 (8): if `f` is a DM morphism of algebraic stacks, then
`Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is unramified. -/
@[stacks 0CPL]
theorem isomComparison_unramified {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (isomComparison f x1 x2) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
