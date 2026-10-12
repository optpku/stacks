/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_23_2_Formal
public import stacks_project.Chap87.Definition_87_23_2_AdicStar
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic

/-!
# Adic morphisms of locally adic* formal algebraic spaces

A morphism of locally adic* formal algebraic spaces is adic when it is
representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A sheaf map `g : U ⟶ V` is the sheaf-colimit map of `Spec` of the quotient
maps induced by `φ`, with `πU` and `πV` the colimit legs of adic power
presentations of `U` and `V`. -/
def IsColimitMapOf {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsAdicRing A] [IsAdicRing B]
    (φ : B →+* A) (I : Ideal A) (J : Ideal B)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} (g : U ⟶ V) : Prop :=
  ∃ (DU DV : ℕ ⥤ 𝒮.bigAffineSite S)
    (eU : ∀ n, ((𝒮.bigAffineToScheme S).obj (DU.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I ^ (n + 1))))
    (eV : ∀ n, ((𝒮.bigAffineToScheme S).obj (DV.obj n)) ≅
      Spec (CommRingCat.of (B ⧸ J ^ (n + 1))))
    (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (iU : cU.pt ≅ U) (iV : cV.pt ≅ V) (τ : DU ⟶ DV)
    (φn : ∀ n, B ⧸ J ^ (n + 1) →+* A ⧸ I ^ (n + 1)),
      Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
        I.FG ∧ J.FG ∧
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            TopologicalRing.Ideal.IsIdealOfDefinition J ∧
              (∀ {i j : ℕ} (f : i ⟶ j),
                IsThickening ((𝒮.bigAffineToScheme S).map (DU.map f))) ∧
                (∀ {i j : ℕ} (f : i ⟶ j),
                  IsThickening ((𝒮.bigAffineToScheme S).map (DV.map f))) ∧
                  (∀ {i j : ℕ} (f : i ⟶ j),
                    CommSq ((𝒮.bigAffineToScheme S).map (DU.map f))
                      (eU i).hom (eU j).hom
                      (Spec.map (CommRingCat.ofHom
                        (Ideal.Quotient.factorPow I
                          (Nat.succ_le_succ (leOfHom f)))))) ∧
                    (∀ {i j : ℕ} (f : i ⟶ j),
                      CommSq ((𝒮.bigAffineToScheme S).map (DV.map f))
                        (eV i).hom (eV j).hom
                        (Spec.map (CommRingCat.ofHom
                          (Ideal.Quotient.factorPow J
                            (Nat.succ_le_succ (leOfHom f)))))) ∧
                      (∀ n,
                        (φn n).comp (Ideal.Quotient.mk (J ^ (n + 1))) =
                          (Ideal.Quotient.mk (I ^ (n + 1))).comp φ) ∧
                        (∀ n,
                          CommSq ((𝒮.bigAffineToScheme S).map (τ.app n))
                            (eU n).hom (eV n).hom
                            (Spec.map (CommRingCat.ofHom (φn n)))) ∧
                          ∀ n,
                            (cU.ι.app n ≫ iU.hom) ≫ g =
                              (𝒮.bigTopology S).sheafifiedRepresentableMap
                                  ((𝒮.bigAffineInclusion S).map (τ.app n)) ≫
                                (cV.ι.app n ≫ iV.hom)

/-- Being the sheaf-colimit map of `Spec (φ_n)` unpacks as adic power
presentations of source and target together with colimit legs compatible with
the stage maps. -/
theorem isColimitMapOf_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsAdicRing A] [IsAdicRing B]
    (φ : B →+* A) (I : Ideal A) (J : Ideal B)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} (g : U ⟶ V) :
    IsColimitMapOf φ I J g ↔
      ∃ (DU DV : ℕ ⥤ 𝒮.bigAffineSite S)
        (eU : ∀ n, ((𝒮.bigAffineToScheme S).obj (DU.obj n)) ≅
          Spec (CommRingCat.of (A ⧸ I ^ (n + 1))))
        (eV : ∀ n, ((𝒮.bigAffineToScheme S).obj (DV.obj n)) ≅
          Spec (CommRingCat.of (B ⧸ J ^ (n + 1))))
        (cU : Cocone (DU ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
        (cV : Cocone (DV ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
        (iU : cU.pt ≅ U) (iV : cV.pt ≅ V) (τ : DU ⟶ DV)
        (φn : ∀ n, B ⧸ J ^ (n + 1) →+* A ⧸ I ^ (n + 1)),
          Nonempty (IsColimit cU) ∧ Nonempty (IsColimit cV) ∧
            I.FG ∧ J.FG ∧
              TopologicalRing.Ideal.IsIdealOfDefinition I ∧
                TopologicalRing.Ideal.IsIdealOfDefinition J ∧
                  (∀ {i j : ℕ} (f : i ⟶ j),
                    IsThickening ((𝒮.bigAffineToScheme S).map (DU.map f))) ∧
                    (∀ {i j : ℕ} (f : i ⟶ j),
                      IsThickening ((𝒮.bigAffineToScheme S).map (DV.map f))) ∧
                      (∀ {i j : ℕ} (f : i ⟶ j),
                        CommSq ((𝒮.bigAffineToScheme S).map (DU.map f))
                          (eU i).hom (eU j).hom
                          (Spec.map (CommRingCat.ofHom
                            (Ideal.Quotient.factorPow I
                              (Nat.succ_le_succ (leOfHom f)))))) ∧
                        (∀ {i j : ℕ} (f : i ⟶ j),
                          CommSq ((𝒮.bigAffineToScheme S).map (DV.map f))
                            (eV i).hom (eV j).hom
                            (Spec.map (CommRingCat.ofHom
                              (Ideal.Quotient.factorPow J
                                (Nat.succ_le_succ (leOfHom f)))))) ∧
                          (∀ n,
                            (φn n).comp (Ideal.Quotient.mk (J ^ (n + 1))) =
                              (Ideal.Quotient.mk (I ^ (n + 1))).comp φ) ∧
                            (∀ n,
                              CommSq ((𝒮.bigAffineToScheme S).map (τ.app n))
                                (eU n).hom (eV n).hom
                                (Spec.map (CommRingCat.ofHom (φn n)))) ∧
                              ∀ n,
                                (cU.ι.app n ≫ iU.hom) ≫ g =
                                  (𝒮.bigTopology S).sheafifiedRepresentableMap
                                      ((𝒮.bigAffineInclusion S).map (τ.app n)) ≫
                                    (cV.ι.app n ≫ iV.hom) := sorry

/-- Definition 87.23.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Assume `X` and `Y` are locally adic*. We say
`f` is an adic morphism if `f` is representable by algebraic spaces. -/
@[stacks 0AQ3]
class Adic {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] (f : X ⟶ Y) : Prop where
  /-- An adic morphism is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f

namespace Adic

/-- The identity morphism of a locally adic* formal algebraic space is adic. -/
instance id {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] : Adic (𝟙 X) := sorry

/-- A morphism of locally adic* formal algebraic spaces that is representable
by algebraic spaces is adic. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] {f : X ⟶ Y}
    (hf : representableByAlgebraicSpaces f) : Adic f := sorry

/-- A morphism of locally adic* formal algebraic spaces is adic iff it is
representable by algebraic spaces. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] (f : X ⟶ Y) :
    Adic f ↔ representableByAlgebraicSpaces f := sorry

/-- An adic morphism has algebraic-space base change along every sheafified
representable. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] (f : X ⟶ Y) [Adic f]
    {U : 𝒮.bigSite S} (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y) :
    IsAlgebraicSpace (pullback ξ f) := sorry

/-- A morphism of locally adic* formal algebraic spaces is adic iff every
commutative square of étale affine charts that are representable by algebraic
spaces has representable-by-algebraic-spaces comparison morphism. -/
theorem iff_charts {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] (f : X ⟶ Y) :
    Adic f ↔
      ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} (g : U ⟶ V)
        (p : U ⟶ X) (q : V ⟶ Y),
        IsAffineFormalAlgebraicSpace U →
          IsAffineFormalAlgebraicSpace V →
            representableByAlgebraicSpaces p →
              representableByAlgebraicSpaces q →
                relativelyEtale p → relativelyEtale q →
                  g ≫ q = p ≫ f → representableByAlgebraicSpaces g := sorry

/-- A morphism of locally adic* formal algebraic spaces is adic iff every
étale affine chart comparison is the sheaf-colimit map of an adic,
equivalently taut, homomorphism in `WAdm^{adic*}`. -/
theorem iff_wAdm {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] (f : X ⟶ Y) :
    Adic f ↔
      ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} (g : U ⟶ V)
        (p : U ⟶ X) (q : V ⟶ Y),
        IsAffineFormalAlgebraicSpace U →
          IsAffineFormalAlgebraicSpace V →
            representableByAlgebraicSpaces p →
              representableByAlgebraicSpaces q →
                relativelyEtale p → relativelyEtale q →
                  g ≫ q = p ≫ f →
                    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
                      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
                      (_ : IsAdicRing A) (_ : IsAdicRing B)
                      (I : Ideal A) (J : Ideal B) (φ : B →+* A),
                        IsColimitMapOf φ I J g ∧ φ.IsAdicHom ∧ φ.IsTaut := sorry

end Adic

/-- For a sheaf map of affine adic* charts that is the colimit of `Spec` of the
quotient maps of a presentation homomorphism, adicness of the homomorphism is
equivalent to adicness of the sheaf map. -/
theorem isAdicHom_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} (g : U ⟶ V)
    [IsAdicStar U] [IsAdicStar V]
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsAdicRing A] [IsAdicRing B]
    (φ : B →+* A) (I : Ideal A) (J : Ideal B)
    (hinduces : IsColimitMapOf φ I J g) :
    φ.IsAdicHom ↔ Adic g := sorry

/-- A presentation homomorphism inducing an étale affine chart comparison as a
sheaf-colimit map of `Spec (φ_n)` is an adic homomorphism whenever the chart is
adic. -/
theorem chart_isAdicHom {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} (g : U ⟶ V)
    [IsAdicStar U] [IsAdicStar V] [Adic g]
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsAdicRing A] [IsAdicRing B]
    (φ : B →+* A) (I : Ideal A) (J : Ideal B)
    (hinduces : IsColimitMapOf φ I J g) :
    φ.IsAdicHom := sorry

end AlgebraicGeometry
