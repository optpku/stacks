module

public import stacks_project.Chap42.Lemma_42_47_3_BaseChange
public import stacks_project.Chap42.Lemma_42_48_2
public import stacks_project.Chap42.Lemma_42_49_2_Construction
public import stacks_project.Chap42.Situation_42_50_1_LocalizedChern

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

section

variable
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    {Z Z' W W' T T' E E' : Scheme.{u}}
    (i : Z ⟶ X.left) (i' : Z' ⟶ X'.left)
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X' ⟶ X) [LocallyOfFiniteType g.left]
    (gZ : Over.mk (i' ≫ X'.hom) ⟶ Over.mk (i ≫ X.hom))
    (squareZ : IsPullback gZ.left
      (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X').left
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X).left g.left)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (b' : W' ⟶ ProjectiveLineFamily.space X') [IsProper b']
    [IsIso (b' ∣_ BivariantClass.GysinAtInfinity.affinePart X')]
    (h : BivariantClass.GysinAtInfinity.compactification X' b' ⟶
      BivariantClass.GysinAtInfinity.compactification X b)
    (hb : IsPullback h.left b' b (ProjectiveLineFamily.map g))
    (gInf : BivariantClass.GysinAtInfinity.infinityFiber X' b' ⟶
      BivariantClass.GysinAtInfinity.infinityFiber X b)
    (hgInf : gInf ≫ BivariantClass.GysinAtInfinity.infinityInclusion X b =
      BivariantClass.GysinAtInfinity.infinityInclusion X' b' ≫ h)
    (squareInf : IsPullback gInf.left
      (BivariantClass.GysinAtInfinity.infinityToX X' b').left
      (BivariantClass.GysinAtInfinity.infinityToX X b).left g.left)
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (t' : T' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X' b').left)
    [IsClosedImmersion t] [IsClosedImmersion t']
    (j : E ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    (j' : E' ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X' b').left)
    [IsClosedImmersion j] [IsClosedImmersion j']
    (cover : Set.range t.base ∪ Set.range j.base = Set.univ)
    (cover' : Set.range t'.base ∪ Set.range j'.base = Set.univ)
    (gT : Over.mk (t' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
      Over.mk (t ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
    (gE : Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
      Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
    [LocallyOfFiniteType gT.left] [LocallyOfFiniteType gE.left]
    (squareT : IsPullback gT.left t' t gInf.left)
    (squareEInf : IsPullback gE.left j' j gInf.left)
    (e : Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
      Over.mk (i ≫ X.hom))
    (e' : Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
      Over.mk (i' ≫ X'.hom))
    [IsProper e.left] [IsProper e'.left]
    (squareE : IsPullback gE.left e'.left e.left gZ.left)
    (factor :
      (Over.homMk j :
          Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
            BivariantClass.GysinAtInfinity.infinityFiber X b) ≫
          BivariantClass.GysinAtInfinity.infinityToX X b =
        e ≫ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (factor' :
      (Over.homMk j' :
          Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
            BivariantClass.GysinAtInfinity.infinityFiber X' b') ≫
          BivariantClass.GysinAtInfinity.infinityToX X' b' =
        e' ≫ (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X'))
    (Q : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q))
    (p : ℕ)

include cover cover' hb hgInf squareInf squareT squareEInf squareE perfect perfect'

/-- Lemma 42.49.2 (1): the Newton bivariant class constructed from the base-changed
compactification, pulled-back complex, and closed part of the infinity fibre is the
restriction of the original Newton class. -/
@[stacks 0GUI]
theorem newtonClassAtZero_eq_restrict
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived
        (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
          ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)))
    (newtonClass : RingedSpace.ModuleDerived E.toRingedSpace → (q : ℕ) →
      BivariantClass δ
        (𝟙 (Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom)))
        (q : ℤ))
    (newtonClass' : RingedSpace.ModuleDerived E'.toRingedSpace → (q : ℕ) →
      BivariantClass δ
        (𝟙 (Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom)))
        (q : ℤ))
    (newtonClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (k : Y ⟶ Over.mk (j ≫
          (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
        [LocallyOfFiniteType k.left],
        IsZero ((RingedSpace.modulePullbackDerived k.left.toShHom).obj
          ((RingedSpace.modulePullbackDerived
            (j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
              Q)) →
          BivariantClass.restrict δ k (𝟙 Y) k IsPullback.of_id_snd (p : ℤ)
            (newtonClass
              ((RingedSpace.modulePullbackDerived
                (j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
                  Q) p) = 0)
    (newtonClass_vanishes_after_pullback' :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (k : Y ⟶ Over.mk (j' ≫
          (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom))
        [LocallyOfFiniteType k.left],
        IsZero ((RingedSpace.modulePullbackDerived k.left.toShHom).obj
          ((RingedSpace.modulePullbackDerived
            (j' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
              ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q))) →
          BivariantClass.restrict δ k (𝟙 Y) k IsPullback.of_id_snd (p : ℤ)
            (newtonClass'
              ((RingedSpace.modulePullbackDerived
                (j' ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
                    ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)) p) = 0)
    (ambientBaseChange :
      newtonClass'
          ((RingedSpace.modulePullbackDerived
            (j' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
              ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)) p =
        BivariantClass.restrict δ gE
          (𝟙 (Over.mk (j' ≫
            (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom))) gE
          IsPullback.of_id_snd (p : ℤ)
          (newtonClass
            ((RingedSpace.modulePullbackDerived
              (j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
                Q) p))
    (localized : BivariantClass δ
      (Over.homMk j :
        Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
          BivariantClass.GysinAtInfinity.infinityFiber X b) (p : ℤ))
    (localized' : BivariantClass δ
      (Over.homMk j' :
        Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
          BivariantClass.GysinAtInfinity.infinityFiber X' b') (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ
      (BivariantClass.GysinAtInfinity.infinityFiber X b) t j (p : ℤ)
      (newtonClass
        ((RingedSpace.modulePullbackDerived
          (j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized)
    (hlocalized' : BivariantClass.IsLocalizedExtension δ
      (BivariantClass.GysinAtInfinity.infinityFiber X' b') t' j' (p : ℤ)
      (newtonClass'
        ((RingedSpace.modulePullbackDerived
          (j' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
            ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)) p)
      localized') :
    BivariantClass.pushforwardComp δ e'
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X')
        (Over.homMk j' :
          Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
            BivariantClass.GysinAtInfinity.infinityFiber X' b')
        (BivariantClass.GysinAtInfinity.infinityToX X' b') factor' (p : ℤ) localized'
        (BivariantClass.gysinAtInfinity δ X' b') =
      BivariantClass.restrict δ gZ
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') g squareZ (p : ℤ)
        (BivariantClass.pushforwardComp δ e
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
          (Over.homMk j :
            Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
              BivariantClass.GysinAtInfinity.infinityFiber X b)
          (BivariantClass.GysinAtInfinity.infinityToX X b) factor (p : ℤ) localized
          (BivariantClass.gysinAtInfinity δ X b)) := sorry

/-- Lemma 42.49.2 (2): the Chern bivariant class constructed from the base-changed
compactification, pulled-back complex, and closed part of the infinity fibre is the
restriction of the original Chern class. -/
@[stacks 0GUI]
theorem chernClassAtZero_eq_restrict
    (restrictionRank : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) 0 p)
    (restrictionRank' : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
      ((RingedSpace.modulePullbackDerived
        (t' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
          ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)) 0 p)
    (chernClass : RingedSpace.ModuleDerived E.toRingedSpace → (q : ℕ) →
      BivariantClass δ
        (𝟙 (Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom)))
        (q : ℤ))
    (chernClass' : RingedSpace.ModuleDerived E'.toRingedSpace → (q : ℕ) →
      BivariantClass δ
        (𝟙 (Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom)))
        (q : ℤ))
    (chernClass_vanishes_after_pullback :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (k : Y ⟶ Over.mk (j ≫
          (BivariantClass.GysinAtInfinity.infinityFiber X b).hom))
        [LocallyOfFiniteType k.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived k.left.toShHom).obj
              ((RingedSpace.modulePullbackDerived
                (j ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
                    Q)) 0 p →
          BivariantClass.restrict δ k (𝟙 Y) k IsPullback.of_id_snd (p : ℤ)
            (chernClass
              ((RingedSpace.modulePullbackDerived
                (j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
                  Q) p) = 0)
    (chernClass_vanishes_after_pullback' :
      ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
        (k : Y ⟶ Over.mk (j' ≫
          (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom))
        [LocallyOfFiniteType k.left],
        Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
            ((RingedSpace.modulePullbackDerived k.left.toShHom).obj
              ((RingedSpace.modulePullbackDerived
                (j' ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
                    ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q))) 0 p →
          BivariantClass.restrict δ k (𝟙 Y) k IsPullback.of_id_snd (p : ℤ)
            (chernClass'
              ((RingedSpace.modulePullbackDerived
                (j' ≫
                  (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
                    ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)) p) = 0)
    (ambientBaseChange :
      chernClass'
          ((RingedSpace.modulePullbackDerived
            (j' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
              ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)) p =
        BivariantClass.restrict δ gE
          (𝟙 (Over.mk (j' ≫
            (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom))) gE
          IsPullback.of_id_snd (p : ℤ)
          (chernClass
            ((RingedSpace.modulePullbackDerived
              (j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj
                Q) p))
    (localized : BivariantClass δ
      (Over.homMk j :
        Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
          BivariantClass.GysinAtInfinity.infinityFiber X b) (p : ℤ))
    (localized' : BivariantClass δ
      (Over.homMk j' :
        Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
          BivariantClass.GysinAtInfinity.infinityFiber X' b') (p : ℤ))
    (hlocalized : BivariantClass.IsLocalizedExtension δ
      (BivariantClass.GysinAtInfinity.infinityFiber X b) t j (p : ℤ)
      (chernClass
        ((RingedSpace.modulePullbackDerived
          (j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q) p)
      localized)
    (hlocalized' : BivariantClass.IsLocalizedExtension δ
      (BivariantClass.GysinAtInfinity.infinityFiber X' b') t' j' (p : ℤ)
      (chernClass'
        ((RingedSpace.modulePullbackDerived
          (j' ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X' b').left).toShHom).obj
            ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)) p)
      localized') :
    BivariantClass.pushforwardComp δ e'
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X')
        (Over.homMk j' :
          Over.mk (j' ≫ (BivariantClass.GysinAtInfinity.infinityFiber X' b').hom) ⟶
            BivariantClass.GysinAtInfinity.infinityFiber X' b')
        (BivariantClass.GysinAtInfinity.infinityToX X' b') factor' (p : ℤ) localized'
        (BivariantClass.gysinAtInfinity δ X' b') =
      BivariantClass.restrict δ gZ
        (Over.homMk i' : Over.mk (i' ≫ X'.hom) ⟶ X') g squareZ (p : ℤ)
        (BivariantClass.pushforwardComp δ e
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
          (Over.homMk j :
            Over.mk (j ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) ⟶
              BivariantClass.GysinAtInfinity.infinityFiber X b)
          (BivariantClass.GysinAtInfinity.infinityToX X b) factor (p : ℤ) localized
          (BivariantClass.gysinAtInfinity δ X b)) := sorry

end

end AlgebraicGeometry.LocalizedChern
