/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_49_1
public import stacks_project.Chap42.Lemma_42_49_3_AtZero
public import stacks_project.Chap42.Lemma_42_47_8_Cutoff
public import stacks_project.Chap42.Lemma_42_47_11_Pullback
public import stacks_project.Chap42.Definition_42_46_3_DerivedChern
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Integral

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived
open RingedSpace.ModuleDerived
open BivariantClass.Cutoff
open ChowCohomology.Nonnegative.Completion

/-- Binary biproducts of perfect derived modules remain perfect. -/
theorem isPerfect_biprod {X : RingedSpace.{u}}
    {E F : RingedSpace.ModuleDerived X}
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hF : RingedSpace.ModuleDerived.IsPerfect F) :
    RingedSpace.ModuleDerived.IsPerfect (E ⊞ F) := sorry

/-- Definedness of derived Chern classes is preserved by binary biproducts. -/
theorem isDefined_biprod {X : Scheme.{u}}
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (hE : ChernClass.Derived.IsDefined E)
    (hF : ChernClass.Derived.IsDefined F) :
    ChernClass.Derived.IsDefined (E ⊞ F) := sorry

/-- A closed subscheme of an `S`-scheme locally of finite type is locally of finite
type over `S`. -/
instance closedOverSourceLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i] :
    LocallyOfFiniteType (Over.mk (i ≫ X.hom)).hom := sorry

/-- The closed immersion `i` remains a closed immersion as a morphism of `S`-schemes. -/
instance instIsClosedImmersion_overHomMk
    {S : Scheme.{u}} {X : Over S} {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i] :
    IsClosedImmersion (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left :=
  ‹IsClosedImmersion i›

/-- Lemma 42.49.7 (1): in the Gysin-at-infinity setup of Lemma 42.49.1, if `Q` and `Q'`
are perfect with defined Chern classes and their restrictions to `T` are degree-zero
finite locally free of ranks strictly less than `p` and `p'`, then in degrees `n < p + p'`
the mixed cutoff series in `A^{(p+p')}(Z ⟶ X)` is ambient-multiplicative: the Chern
classes `c_n` of the restrictions to the zero fibre multiply, while the localized
classes `c'_i` of Lemma 42.49.1 begin only at the cutoff. -/
@[stacks 0FAY]
theorem cutoffChernClassAtZero_biprod_lt
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ}
    [IsDimensionFunction δ] {X : Over S} [LocallyOfFiniteType X.hom]
    {Z W T : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q Q' : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfectQ : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfectQ' : RingedSpace.ModuleDerived.IsPerfect Q')
    (definedQ : ChernClass.Derived.IsDefined Q)
    (definedQ' : ChernClass.Derived.IsDefined Q')
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p p' : ℕ)
    (restrictionRankQ : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
        Q) 0 p)
    (restrictionRankQ' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
        Q') 0 p')
    (classes : ChernClass.Theory δ X.hom) (n : ℕ) (hn : n < p + p') :
    totalClass δ X.hom classes
        ((RingedSpace.modulePullbackDerived
          (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj
          (Q ⊞ Q'))
        (RingedSpace.modulePullbackDerived_isPerfect
          (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom
          (Q ⊞ Q') (isPerfect_biprod perfectQ perfectQ'))
        (IsDefined.pullback
          (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left
          (isDefined_biprod definedQ definedQ')) n =
      mul δ X.hom
        (totalClass δ X.hom classes
          ((RingedSpace.modulePullbackDerived
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj Q)
          (RingedSpace.modulePullbackDerived_isPerfect
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom
            Q perfectQ)
          (IsDefined.pullback
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left definedQ))
        (totalClass δ X.hom classes
          ((RingedSpace.modulePullbackDerived
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj Q')
          (RingedSpace.modulePullbackDerived_isPerfect
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom
            Q' perfectQ')
          (IsDefined.pullback
            (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left definedQ')) n :=
  sorry

/-- Lemma 42.49.7 (2): in the same setup, with localized classes `c'_k(Q)` as in
Lemma 42.49.1, the mixed cutoff Chern series of `Q ⊞ Q'` in `A^{(p+p')}(Z ⟶ X)` equals
the mixed product of the cutoff series of `Q` and of `Q'` in degrees `p + p' ≤ n`. -/
@[stacks 0FAY]
theorem cutoffChernClassAtZero_biprod
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ}
    [IsDimensionFunction δ] {X : Over S} [LocallyOfFiniteType X.hom]
    {Z W T : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (Q Q' : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfectQ : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfectQ' : RingedSpace.ModuleDerived.IsPerfect Q')
    (definedQ : ChernClass.Derived.IsDefined Q)
    (definedQ' : ChernClass.Derived.IsDefined Q')
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p p' : ℕ)
    (restrictionRankQ : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
        Q) 0 p)
    (restrictionRankQ' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
        Q') 0 p')
    (classes : ChernClass.Theory δ X.hom)
    (localizedQ localizedQ' localizedBiprod :
      (k : ℕ) → BivariantClass δ
        (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (k : ℤ))
    (hlocalizedQ : ∀ k : ℕ, p ≤ k →
      IsInfinityLocalizedExtension δ i b t (k : ℤ)
        (totalClass δ (infinityCenter i b).hom
          (classes.reanchor (infinityCenter i b))
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
            Q)
          (RingedSpace.modulePullbackDerived_isPerfect
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
            Q perfectQ)
          (IsDefined.pullback
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
            definedQ) k)
        (localizedQ k))
    (hlocalizedQ' : ∀ k : ℕ, p' ≤ k →
      IsInfinityLocalizedExtension δ i b t (k : ℤ)
        (totalClass δ (infinityCenter i b).hom
          (classes.reanchor (infinityCenter i b))
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
            Q')
          (RingedSpace.modulePullbackDerived_isPerfect
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
            Q' perfectQ')
          (IsDefined.pullback
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
            definedQ') k)
        (localizedQ' k))
    (hlocalizedBiprod : ∀ k : ℕ, p + p' ≤ k →
      IsInfinityLocalizedExtension δ i b t (k : ℤ)
        (totalClass δ (infinityCenter i b).hom
          (classes.reanchor (infinityCenter i b))
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
            (Q ⊞ Q'))
          (RingedSpace.modulePullbackDerived_isPerfect
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
            (Q ⊞ Q') (isPerfect_biprod perfectQ perfectQ'))
          (IsDefined.pullback
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
            (isDefined_biprod definedQ definedQ')) k)
        (localizedBiprod k))
    (n : ℕ) (hn : p + p' ≤ n) :
    classAtZero δ i b n (localizedBiprod n) =
      mixedMul δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p p' n hn
        (fun k ↦ cutoffChernClass δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p k
          (totalClass δ X.hom classes
            ((RingedSpace.modulePullbackDerived
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj Q)
            (RingedSpace.modulePullbackDerived_isPerfect
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom
              Q perfectQ)
            (IsDefined.pullback
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left definedQ) k)
          (classAtZero δ i b k (localizedQ k)))
        (fun m ↦ cutoffChernClass δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p' m
          (totalClass δ X.hom classes
            ((RingedSpace.modulePullbackDerived
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom).obj Q')
            (RingedSpace.modulePullbackDerived_isPerfect
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left.toShHom
              Q' perfectQ')
            (IsDefined.pullback
              (BivariantClass.GysinAtInfinity.zeroSectionLift X b).left definedQ') m)
          (classAtZero δ i b m (localizedQ' m))) :=
  sorry

end AlgebraicGeometry.LocalizedChern
