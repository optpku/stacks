module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleInverseImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleDerivedComparison
import StacksCheckRecall

@[expose] public section

/-!
Lemma 59.100.6 (0DDS) compares small étale and big fppf abelian sheaf cohomology via
`a_X = π_X ∘ ε_X`.  The reusable inverse-image functors and the six source clauses are owned
by `AlgebraicGeometry.Scheme.FppfEtale`; this chapter file is a labeled check facade.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FppfEtale
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

universe u

/- Lemma 59.100.6 (1a): ε_{X,*}(a_X⁻¹ F) ≅ π_X⁻¹ F. -/
@[stacks 0DDS]
#check (AlgebraicGeometry.Scheme.FppfEtale.aInverse_unit_isIso :
    ∀ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    IsIso (aInverse_unit X F))

/- Lemma 59.100.6 (1b): R^i ε_{X,*}(a_X⁻¹ F) = 0 for i > 0. -/
@[stacks 0DDS]
#check (AlgebraicGeometry.Scheme.FppfEtale.aInverse_higherDirectImage_isZero :
    ∀ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) (hi : 0 < i),
    IsZero
      (((epsilonPushforward X).rightDerived i).obj ((aInverseAb X).obj F)))

/- Lemma 59.100.6 (2): for finite f, a_Y⁻¹(R^i f_small,* F) ≅ R^i f_big,fppf,*(a_X⁻¹ F). -/
@[stacks 0DDS]
#check (AlgebraicGeometry.Scheme.FppfEtale.finite_higherDirectImage :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ),
    IsIsomorphic
      ((aInverseAb Y).obj (((smallPushforwardAb f).rightDerived i).obj F))
      (((fppfPushforwardAb f).rightDerived i).obj ((aInverseAb X).obj F)))

/- Lemma 59.100.6 (3): for K in D⁺(X_étale), π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K) is an isomorphism. -/
@[stacks 0DDS]
#check (AlgebraicGeometry.Scheme.FppfEtale.derivedUnit_isIso :
    ∀ {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
    IsIso ((Derived.Plus.unit
      (Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage) X).app
        ((piInverseImagePlus X).obj K)))

/- Lemma 59.100.6 (4): for finite f and K in D⁺(X_étale),
a_Y⁻¹(Rf_small,* K) ≅ Rf_big,fppf,*(a_X⁻¹ K). -/
@[stacks 0DDS]
#check (AlgebraicGeometry.Scheme.FppfEtale.finite_derivedPushforward :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((aInverseAbPlus Y).obj
        ((Adjunction.Derived.Plus.right (smallPushforwardAb f)).obj K))
      ((Derived.Over.Plus.pushforward fppfTopology f).obj
        ((aInverseAbPlus X).obj K)))

/- Lemma 59.100.6 (5): for proper f and K in D⁺(X_étale) with torsion cohomology sheaves,
a_Y⁻¹(Rf_small,* K) ≅ Rf_big,fppf,*(a_X⁻¹ K). -/
@[stacks 0DDS]
#check (AlgebraicGeometry.Scheme.FppfEtale.proper_torsion_derivedPushforward :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K),
    IsIsomorphic
      ((aInverseAbPlus Y).obj
        ((Adjunction.Derived.Plus.right (smallPushforwardAb f)).obj K))
      ((Derived.Over.Plus.pushforward fppfTopology f).obj
        ((aInverseAbPlus X).obj K)))

end
