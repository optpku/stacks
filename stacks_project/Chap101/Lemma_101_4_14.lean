module

public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Unramified or locally quasi-finite fppf covers imply DM or quasi-DM

A surjective, flat, locally finitely presented morphism from an algebraic
space to an algebraic stack that is unramified (equivalently étale) implies
the target is DM, and the locally quasi-finite case implies quasi-DM.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Etale

/-- A flat, locally finitely presented, unramified morphism of algebraic stacks
representable by algebraic spaces is étale. -/
theorem of_unramified {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    (h_unramified : has (@AlgebraicSpace.Unramified S) f) : Etale f :=
  sorry

end Etale

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.DeligneMumfordStack

/-- A surjective, flat, locally finitely presented, unramified morphism from an
algebraic space to an algebraic stack exhibits the target as a Deligne-Mumford
stack. -/
theorem of_unramified {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    (h_unramified : Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f) :
    DeligneMumfordStack X :=
  sorry

end AlgebraicGeometry.DeligneMumfordStack

namespace AlgebraicGeometry.AlgebraicStack

namespace IsDM

/-- Lemma 101.4.14 (1): Let `X` be an algebraic stack. Let `W` be an algebraic
space, and let `f : W.toGroupoids ⟶ X` be a surjective, flat, locally finitely
presented morphism. If `f` is unramified (i.e., étale, i.e., `X` is
Deligne-Mumford), then `X` is DM. -/
@[stacks 06MB]
theorem of_unramified {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    (h_unramified : Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f) :
    IsDM X :=
  sorry

end IsDM

namespace IsQuasiDM

/-- Lemma 101.4.14 (2): Let `X` be an algebraic stack. Let `W` be an algebraic
space, and let `f : W.toGroupoids ⟶ X` be a surjective, flat, locally finitely
presented morphism. If `f` is locally quasi-finite, then `X` is quasi-DM. -/
@[stacks 06MB]
theorem of_locallyQuasiFinite {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    (h_locallyQuasiFinite :
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f) :
    IsQuasiDM X :=
  sorry

end IsQuasiDM

end AlgebraicGeometry.AlgebraicStack
