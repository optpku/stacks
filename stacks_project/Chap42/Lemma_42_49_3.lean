module

public import stacks_project.Chap42.Lemma_42_49_3_AtZero
public import stacks_project.Chap42.Lemma_42_47_2_Independence
public import stacks_project.Chap42.Lemma_42_47_3_BaseChange
public import stacks_project.Chap42.Situation_42_50_1_LocalizedChern

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Lemma 42.49.3 (1): the Newton class at zero obtained from a localized extension is
independent of the auxiliary closed subscheme of the infinity fibre. -/
@[stacks 0FAU]
theorem newtonClassAtZero_eq_of_closedSubschemes
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t] [IsClosedImmersion t']
    (cover : Set.range t.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (cover' : Set.range t'.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (p : ℕ)
    (restrictionZero : IsZero ((RingedSpace.modulePullbackDerived
      (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (restrictionZero' : IsZero ((RingedSpace.modulePullbackDerived
      (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (newtonClass : RingedSpace.ModuleDerived (infinityCenter i b).left.toRingedSpace →
      (q : ℕ) → BivariantClass delta
        (𝟙 (infinityCenter i b)) (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h : Y ⟶ infinityCenter i b) [LocallyOfFiniteType h.left],
        IsZero ((RingedSpace.modulePullbackDerived h.left.toShHom).obj
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)) →
          BivariantClass.restrict delta h (𝟙 Y) h IsPullback.of_id_snd (p : ℤ)
            (newtonClass
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
              p) = 0)
    (localized localized' : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (hlocalized : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (newtonClass
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized)
    (hlocalized' : IsInfinityLocalizedExtension delta i b t' (p : ℤ)
      (newtonClass
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized') :
    classAtZero delta i b (p : ℤ) localized =
      classAtZero delta i b (p : ℤ) localized' := sorry

/-- Lemma 42.49.3 (2): the Chern class at zero obtained from a localized extension is
independent of the auxiliary closed subscheme of the infinity fibre. -/
@[stacks 0FAU]
theorem chernClassAtZero_eq_of_closedSubschemes
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t] [IsClosedImmersion t']
    (cover : Set.range t.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (cover' : Set.range t'.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p)
    (restrictionRank' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p)
    (chernClass : RingedSpace.ModuleDerived (infinityCenter i b).left.toRingedSpace →
      (q : ℕ) → BivariantClass delta
        (𝟙 (infinityCenter i b)) (q : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h : Y ⟶ infinityCenter i b) [LocallyOfFiniteType h.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived h.left.toShHom).obj
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
            0 p →
          BivariantClass.restrict delta h (𝟙 Y) h IsPullback.of_id_snd (p : ℤ)
            (chernClass
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
              p) = 0)
    (localized localized' : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (hlocalized : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (chernClass
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized)
    (hlocalized' : IsInfinityLocalizedExtension delta i b t' (p : ℤ)
      (chernClass
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized') :
    classAtZero delta i b (p : ℤ) localized =
      classAtZero delta i b (p : ℤ) localized' := sorry

/-- Lemma 42.49.3 (3): pulling a perfect complex back along a proper modification
which is an isomorphism over the affine part does not change its Newton class at zero. -/
@[stacks 0FAU]
theorem newtonClassAtZero_eq_of_modification
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W W' T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (g : W' ⟶ W) [IsProper g]
    [IsIso (g ∣_ (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X))]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.modulePullbackDerived g.toShHom).obj Q))
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b) ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    [IsProper gInf.left]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (squareInf : IsPullback
      (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left gInf.left g
      (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b)).left)
    [IsClosedImmersion t] [IsClosedImmersion t']
    (gT : Over.mk (t' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b)).hom) ⟶
      Over.mk (t ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
    (squareT : IsPullback gT.left t' t gInf.left)
    (cover : Set.range t.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (cover' : Set.range t'.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (p : ℕ)
    (restrictionZero : IsZero ((RingedSpace.modulePullbackDerived
      (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (restrictionZero' : IsZero ((RingedSpace.modulePullbackDerived
      (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
        ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)))
    (newtonClass : RingedSpace.ModuleDerived (infinityCenter i b).left.toRingedSpace →
      (q : ℕ) → BivariantClass delta
        (𝟙 (infinityCenter i b)) (q : ℤ))
    (newtonClass' : RingedSpace.ModuleDerived
        (infinityCenter i (g ≫ b)).left.toRingedSpace →
      (q : ℕ) → BivariantClass delta
        (𝟙 (infinityCenter i (g ≫ b))) (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h : Y ⟶ infinityCenter i b) [LocallyOfFiniteType h.left],
        IsZero ((RingedSpace.modulePullbackDerived h.left.toShHom).obj
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)) →
          BivariantClass.restrict delta h (𝟙 Y) h IsPullback.of_id_snd (p : ℤ)
            (newtonClass
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
              p) = 0)
    (newtonClass_vanishes_after_pullback' :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h : Y ⟶ infinityCenter i (g ≫ b)) [LocallyOfFiniteType h.left],
        IsZero ((RingedSpace.modulePullbackDerived h.left.toShHom).obj
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
            ((RingedSpace.modulePullbackDerived g.toShHom).obj Q))) →
          BivariantClass.restrict delta h (𝟙 Y) h IsPullback.of_id_snd (p : ℤ)
            (newtonClass'
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
                ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) p) = 0)
    (ambientBaseChange :
      newtonClass'
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
            ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) p =
        BivariantClass.restrict delta
          (infinityCenterMap i b (g ≫ b) gInf
            (BivariantClass.GysinAtInfinity.infinityMap_toX_of_isPullback
              X b g gInf squareInf))
          (𝟙 (infinityCenter i (g ≫ b)))
          (infinityCenterMap i b (g ≫ b) gInf
            (BivariantClass.GysinAtInfinity.infinityMap_toX_of_isPullback
              X b g gInf squareInf))
          IsPullback.of_id_snd (p : ℤ)
          (newtonClass
            ((RingedSpace.modulePullbackDerived
              ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                  (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p))
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (localized' : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (hlocalized : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (newtonClass
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized)
    (hlocalized' : IsInfinityLocalizedExtension delta i (g ≫ b) t' (p : ℤ)
      (newtonClass'
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
          ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) p)
      localized') :
    classAtZero delta i b (p : ℤ) localized =
      classAtZero delta i (g ≫ b) (p : ℤ) localized' := sorry

/-- Lemma 42.49.3 (4): pulling a perfect complex back along a proper modification
which is an isomorphism over the affine part does not change its Chern class at zero. -/
@[stacks 0FAU]
theorem chernClassAtZero_eq_of_modification
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W W' T T' : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (g : W' ⟶ W) [IsProper g]
    [IsIso (g ∣_ (b ⁻¹ᵁ BivariantClass.GysinAtInfinity.affinePart X))]
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.modulePullbackDerived g.toShHom).obj Q))
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b) ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    [IsProper gInf.left]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    [IsClosedImmersion
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left]
    (squareInf : IsPullback
      (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left gInf.left g
      (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b)).left)
    [IsClosedImmersion t] [IsClosedImmersion t']
    (gT : Over.mk (t' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X (g ≫ b)).hom) ⟶
      Over.mk (t ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
    (squareT : IsPullback gT.left t' t gInf.left)
    (cover : Set.range t.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (cover' : Set.range t'.base ∪ Set.range
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left.base = Set.univ)
    (p : ℕ)
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p)
    (restrictionRank' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
          ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) 0 p)
    (chernClass : RingedSpace.ModuleDerived (infinityCenter i b).left.toRingedSpace →
      (q : ℕ) → BivariantClass delta
        (𝟙 (infinityCenter i b)) (q : ℤ))
    (chernClass' : RingedSpace.ModuleDerived
        (infinityCenter i (g ≫ b)).left.toRingedSpace →
      (q : ℕ) → BivariantClass delta
        (𝟙 (infinityCenter i (g ≫ b))) (q : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h : Y ⟶ infinityCenter i b) [LocallyOfFiniteType h.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived h.left.toShHom).obj
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
            0 p →
          BivariantClass.restrict delta h (𝟙 Y) h IsPullback.of_id_snd (p : ℤ)
            (chernClass
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q)
              p) = 0)
    (chernClass_vanishes_after_pullback' :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (h : Y ⟶ infinityCenter i (g ≫ b)) [LocallyOfFiniteType h.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived h.left.toShHom).obj
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
                ((RingedSpace.modulePullbackDerived g.toShHom).obj Q))) 0 p →
          BivariantClass.restrict delta h (𝟙 Y) h IsPullback.of_id_snd (p : ℤ)
            (chernClass'
              ((RingedSpace.modulePullbackDerived
                ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
                    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
                ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) p) = 0)
    (ambientBaseChange :
      chernClass'
          ((RingedSpace.modulePullbackDerived
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
            ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) p =
        BivariantClass.restrict delta
          (infinityCenterMap i b (g ≫ b) gInf
            (BivariantClass.GysinAtInfinity.infinityMap_toX_of_isPullback
              X b g gInf squareInf))
          (𝟙 (infinityCenter i (g ≫ b)))
          (infinityCenterMap i b (g ≫ b) gInf
            (BivariantClass.GysinAtInfinity.infinityMap_toX_of_isPullback
              X b g gInf squareInf))
          IsPullback.of_id_snd (p : ℤ)
          (chernClass
            ((RingedSpace.modulePullbackDerived
              ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                  (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
                (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p))
    (localized : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (localized' : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (hlocalized : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (chernClass
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized)
    (hlocalized' : IsInfinityLocalizedExtension delta i (g ≫ b) t' (p : ℤ)
      (chernClass'
        ((RingedSpace.modulePullbackDerived
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X (g ≫ b))
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X (g ≫ b)).left).toShHom).obj
          ((RingedSpace.modulePullbackDerived g.toShHom).obj Q)) p)
      localized') :
    classAtZero delta i b (p : ℤ) localized =
      classAtZero delta i (g ≫ b) (p : ℤ) localized' := sorry

end AlgebraicGeometry.LocalizedChern
