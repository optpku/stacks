module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.AbelianComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.DerivedComparison
import StacksCheckRecall

/-!
# Lemma 59.102.5

Torsion abelian small-étale sheaves and bounded-below complexes with torsion cohomology
satisfy the ph/étale comparison and proper direct-image identities.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PhComparison
open CategoryTheory.GrothendieckTopology

universe u

/- Lemma 59.102.5 (1a): the comparison unit identifies the degree-zero direct image. -/
@[stacks 0DE4] #check (AlgebraicGeometry.Scheme.PhComparison.epsilon_pushforward_aInverseImage_unit_isIso :
    ∀ {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion),
    IsIso
      ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1} (etale_le_ph S) X).unit.app
        ((piInverseImage X).obj F)))

/- Lemma 59.102.5 (1b): positive-degree comparison direct images vanish. -/
@[stacks 0DE4] #check (AlgebraicGeometry.Scheme.PhComparison.epsilon_rightDerived_aInverseImage_isZero :
    ∀ {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i),
    IsZero
      (((comparisonTopologyPushforwardAb (etale_le_ph S) X).rightDerived i).obj
        ((aInverseImage X).obj F)))

/- Lemma 59.102.5 (2): proper higher direct images commute with small-to-ph inverse image. -/
@[stacks 0DE4] #check (AlgebraicGeometry.Scheme.PhComparison.proper_aInverseImage_higherDirectImage :
    ∀ {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (hf : properOver S f)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ),
    IsIsomorphic
      ((aInverseImage Y).obj (((smallPushforwardAb f.left).rightDerived i).obj F))
      ((Derived.Over.pushforwardDegree (Scheme.bigPhSite S) f i).obj
        ((aInverseImage X).obj F)))

/- Lemma 59.102.5 (3): the derived comparison unit is an isomorphism. -/
@[stacks 0DE4] #check (AlgebraicGeometry.Scheme.PhComparison.plus_piInverseImage_unit_isIso :
    ∀ {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K),
    IsIso
      ((Derived.Plus.unit (etale_le_ph X) (Over.mk (𝟙 X))).app
        ((plusPiInverseImage (Over.mk (𝟙 X))).obj K)))

/- Lemma 59.102.5 (4): the proper derived direct-image comparison is an isomorphism. -/
@[stacks 0DE4] #check (AlgebraicGeometry.Scheme.PhComparison.proper_plusSmallPhPushforward_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K),
    IsIso ((plusSmallPhPushforwardHom f).app K))
