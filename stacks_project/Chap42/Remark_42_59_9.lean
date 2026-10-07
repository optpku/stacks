module

public import stacks_project.Chap42.Lemma_42_59_8
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Reanchor
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Evaluation
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle

/-- Integer grading identity comparing Gysin-then-Chern and Chern-then-Gysin cap degrees. -/
theorem gysin_chern_cap_degree (n : ℤ) (i r t : ℕ) :
    n - (i : ℤ) - ((r : ℤ) + (-(t : ℤ))) =
      n - ((r : ℤ) + (-(t : ℤ))) - (i : ℤ) :=
  sorry

/-- Remark 42.59.9 (1): in Situation 42.7.1, if `f : X ⟶ Y` is a local complete intersection
morphism of schemes locally of finite type over `S` for which a Gysin map exists, then the
Gysin class commutes with the operational Chern class `cᵢ(E)`. -/
@[stacks 0FF8]
theorem gysin_commute_chernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfFiniteType f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (classes : ChernClass.Theory δ Y.hom)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    Commute δ (𝟙 Y) f (classes.baseComponent Y E i)
      (bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
        (overHom_eq_over ι ▸
          globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
            (ofNormalSheaf ι.left r e) D r)
        (flatPullback δ σ t)) :=
  sorry

/-- Remark 42.59.9 (2): in the same situation, the Gysin class likewise commutes with the
degree-`i` integer Newton class underlying the Chern character. -/
@[stacks 0FF8]
theorem gysin_commute_newtonClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfFiniteType f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (classes : ChernClass.Theory δ Y.hom)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    Commute δ (𝟙 Y) f (ChernPolynomial.Newton.value δ Y.hom classes E i)
      (bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
        (overHom_eq_over ι ▸
          globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
            (ofNormalSheaf ι.left r e) D r)
        (flatPullback δ σ t)) :=
  sorry

/-- Remark 42.59.9 (3): if in addition `X` and `Y` satisfy Lemma 42.42.1 and `Y` is
Cohen–Macaulay, then `f^![Y] = [X]`. -/
@[stacks 0FF8]
theorem gysin_cap_fundamentalClass_id
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfFiniteType f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (hX : ∀ x : X.left, ∃ n, IsGenericDimensionIndex X.hom δ x n)
    (hY : ∀ y : Y.left, ∃ n, IsGenericDimensionIndex Y.hom δ y n)
    [Scheme.CohenMacaulay Y.left] (n : ℤ) :
    (bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
        (overHom_eq_over ι ▸
          globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
            (ofNormalSheaf ι.left r e) D r)
        (flatPullback δ σ t)).cap (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst n
      (fundamentalClass_mk δ Y.hom n) =
      fundamentalClass_mk δ X.hom (n - ((r : ℤ) + (-(t : ℤ)))) :=
  sorry

/-- Remark 42.59.9 (4): under the hypotheses of (1) and (3),
`f^! (cᵢ(E) ∩ [Y]) = cᵢ(f^* E) ∩ [X]`. -/
@[stacks 0FF8]
theorem gysin_cap_chernClass_fundamentalClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfFiniteType f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (classes : ChernClass.Theory δ Y.hom)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ)
    (hX : ∀ x : X.left, ∃ n, IsGenericDimensionIndex X.hom δ x n)
    (hY : ∀ y : Y.left, ∃ n, IsGenericDimensionIndex Y.hom δ y n)
    [Scheme.CohenMacaulay Y.left] (n : ℤ) :
    (bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
        (overHom_eq_over ι ▸
          globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
            (ofNormalSheaf ι.left r e) D r)
        (flatPullback δ σ t)).cap (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst (n - (i : ℤ))
      ((classes.baseComponent Y E i).cap (𝟙 Y) (𝟙 Y) (𝟙 Y) IsPullback.of_id_snd n
        (fundamentalClass_mk δ Y.hom n)) =
      gysin_chern_cap_degree n i r t ▸
        (classes.baseComponent X ((Scheme.Modules.pullback f.left).obj E) i).cap
          (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd (n - ((r : ℤ) + (-(t : ℤ))))
          (fundamentalClass_mk δ X.hom (n - ((r : ℤ) + (-(t : ℤ))))) :=
  sorry

/-- Remark 42.59.9 (5): under the hypotheses of (2) and (3), the same identity holds for the
degree-`i` integer Newton class underlying the Chern character. -/
@[stacks 0FF8]
theorem gysin_cap_newtonClass_fundamentalClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfFiniteType f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (classes : ChernClass.Theory δ Y.hom)
    (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ)
    (hX : ∀ x : X.left, ∃ n, IsGenericDimensionIndex X.hom δ x n)
    (hY : ∀ y : Y.left, ∃ n, IsGenericDimensionIndex Y.hom δ y n)
    [Scheme.CohenMacaulay Y.left] (n : ℤ) :
    (bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
        (overHom_eq_over ι ▸
          globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
            (ofNormalSheaf ι.left r e) D r)
        (flatPullback δ σ t)).cap (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst (n - (i : ℤ))
      ((ChernPolynomial.Newton.value δ Y.hom classes E i).cap
        (𝟙 Y) (𝟙 Y) (𝟙 Y) IsPullback.of_id_snd n (fundamentalClass_mk δ Y.hom n)) =
      gysin_chern_cap_degree n i r t ▸
        (ChernPolynomial.Newton.value δ X.hom (classes.reanchor X)
            ((Scheme.Modules.pullback f.left).obj E) i).cap
          (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_snd (n - ((r : ℤ) + (-(t : ℤ))))
          (fundamentalClass_mk δ X.hom (n - ((r : ℤ) + (-(t : ℤ))))) :=
  sorry

end AlgebraicGeometry.BivariantClass
