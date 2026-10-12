/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_62_1_IntersectionProduct
public import stacks_project.Chap42.Lemma_42_62_5_IntersectionProduct
public import stacks_project.Chap42.Proposition_42_60_2
public import stacks_project.Chap42.«42_37_1_1_FundamentalCycle»
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace SchemeOverField

/-- The structure morphism of the chosen terminal scheme over a field is locally of
finite type. -/
instance instTerminalLocallyOfFiniteType :
    LocallyOfFiniteType (⊤_ (SchemeOverField k)).hom := sorry

/-- Smoothness of `X` over `k` is smoothness of `terminal.from X`. -/
instance instSmooth_terminalFrom (X : SchemeOverField k) [Smooth X.hom] :
    Smooth (terminal.from X).left := sorry

/-- Equidimensionality of `X` over `k` in dimension `d` is the corresponding relative
dimension of `terminal.from X`. -/
instance instRelativeDimension_terminalFrom (X : SchemeOverField k) (d : ℕ)
    [RelativeDimension X.hom d] :
    RelativeDimension (terminal.from X).left d := sorry

end SchemeOverField

namespace ChowGroup

/-- The degree-`d` fundamental Chow class `[X]_d` of a scheme locally of finite type over a
field. -/
noncomputable def relativeFundamentalClass (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) :
    RelativeChow (fun _ ↦ 0) X (d : ℤ) :=
  @chowClass X.left
    (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
      inferInstance
      (@instUniversallyCatenarySpec k inferInstance
        instUniversallyCatenaryRingOfField.{u, u}).toIsLocallyNoetherian)
    (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (d : ℤ)
    (@CycleGroup.fundamental X.left
      (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
        inferInstance
        (@instUniversallyCatenarySpec k inferInstance
          instUniversallyCatenaryRingOfField.{u, u}).toIsLocallyNoetherian)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (d : ℤ))

/-- The class `[X]_d` is the Chow class of the degree-`d` fundamental cycle. -/
theorem relativeFundamentalClass_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) :
    relativeFundamentalClass X d =
      @chowClass X.left
        (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
          inferInstance
          (@instUniversallyCatenarySpec k inferInstance
            instUniversallyCatenaryRingOfField.{u, u}).toIsLocallyNoetherian)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (d : ℤ)
        (@CycleGroup.fundamental X.left
          (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
            inferInstance
            (@instUniversallyCatenarySpec k inferInstance
              instUniversallyCatenaryRingOfField.{u, u}).toIsLocallyNoetherian)
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (d : ℤ)) := sorry

end ChowGroup

namespace BivariantClass

/-- Capping with `[X]_d`, as a map `A^p(X) → CH_{d-p}(X)`. -/
noncomputable def capFundamental (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X) p) :
    RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p) :=
  c.cap (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_fst (d : ℤ)
    (ChowGroup.relativeFundamentalClass X d)

/-- Unfold the source operation `c ↦ c ∩ [X]_d`. -/
theorem capFundamental_apply (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X) p) :
    capFundamental X d p c =
      c.cap (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_fst (d : ℤ)
        (ChowGroup.relativeFundamentalClass X d) := sorry

/-- Capping with `[X]_d` sends the zero class to zero. -/
theorem capFundamental_zero (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ) :
    capFundamental X d p 0 = 0 := sorry

/-- Capping with `[X]_d` preserves addition. -/
theorem capFundamental_add (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ)
    (c c' : BivariantClass (fun _ ↦ 0) (𝟙 X) p) :
    capFundamental X d p (c + c') =
      capFundamental X d p c + capFundamental X d p c' := sorry

/-- Capping with `[X]_d` as an additive map. -/
noncomputable def capFundamentalAddHom (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ) :
    BivariantClass (fun _ ↦ 0) (𝟙 X) p →+
      RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p) where
  toFun := capFundamental X d p
  map_zero' := capFundamental_zero X d p
  map_add' := capFundamental_add X d p

/-- The additive map `capFundamentalAddHom` is capping with `[X]_d`. -/
theorem capFundamentalAddHom_apply (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X) p) :
    capFundamentalAddHom X d p c = capFundamental X d p c := sorry

/-- The source inverse of capping with `[X]_d`. -/
noncomputable def capFundamentalInv (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ) :
    RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p) →
      BivariantClass (fun _ ↦ 0) (𝟙 X) p :=
  Function.invFun (capFundamental X d p)

/-- Evaluation of the inverse of capping with `[X]_d`. -/
theorem capFundamentalInv_apply (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (d : ℕ) (p : ℤ)
    (alpha : RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p)) :
    capFundamentalInv X d p alpha = Function.invFun (capFundamental X d p) alpha := sorry

/-- The canonical additive identification `A^p(X) ≃+ CH_{d-p}(X)` given by capping with
`[X]_d`, for `X` smooth and equidimensional of dimension `d` over a field. -/
noncomputable def capFundamentalEquiv (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ) :
    BivariantClass (fun _ ↦ 0) (𝟙 X) p ≃+
      RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p) where
  toFun := capFundamental X d p
  invFun := capFundamentalInv X d p
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `capFundamentalEquiv` is capping with `[X]_d`. -/
theorem capFundamentalEquiv_apply (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X) p) :
    capFundamentalEquiv X d p c = capFundamental X d p c := sorry

/-- The inverse map of `capFundamentalEquiv` is `capFundamentalInv`. -/
theorem capFundamentalEquiv_symm_apply (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) [RelativeDimension X.hom d] (p : ℤ)
    (alpha : RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p)) :
    (capFundamentalEquiv X d p).symm alpha = capFundamentalInv X d p alpha := sorry

/-- Transport a bivariant class along `𝟙 X ≫ 𝟙 X = 𝟙 X`. -/
def idComp_id (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X ≫ 𝟙 X) p) :
    BivariantClass (fun _ ↦ 0) (𝟙 X) p :=
  Category.id_comp (𝟙 X) ▸ c

/-- Unfold transport along `𝟙 X ≫ 𝟙 X = 𝟙 X`. -/
theorem idComp_id_eq (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X ≫ 𝟙 X) p) :
    idComp_id X p c = Category.id_comp (𝟙 X) ▸ c := sorry

/-- The grading identity comparing composition of caps with `[X]_d` to the intersection
product degree. -/
theorem capFundamental_comp_degree (d : ℕ) (p q : ℤ) :
    (d : ℤ) - p + ((d : ℤ) - q) - d = (d : ℤ) - (p + q) := sorry

/-- Via the identification by `[X]_d`, composition of bivariant classes on `𝟙 X` becomes
the intersection product of Chow classes. -/
theorem capFundamental_comp (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d]
    [IsFiniteLocallyFreeOfRank d (conormalSheaf (ChowGroup.diagonal X).left)]
    (D : ChowGroup.DiagonalSpecialization X d) (p q : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X) p)
    (c' : BivariantClass (fun _ ↦ 0) (𝟙 X) q) :
    capFundamental X d (p + q)
        (idComp_id X (p + q) (comp (fun _ ↦ 0) (𝟙 X) (𝟙 X) c c')) =
      castRelativeDegree (fun _ ↦ 0) (capFundamental_comp_degree d p q)
        (ChowGroup.intersectionProduct X d D (capFundamental X d p c)
          (capFundamental X d q c')) := sorry

/-- Composition with the smooth Gysin class of the structure morphism, as used to factor
capping with `[X]_d`. -/
noncomputable def capFundamental_compSmooth (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) [RelativeDimension X.hom d] (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X) p) :
    BivariantClass (fun _ ↦ 0) (𝟙 X ≫ terminal.from X) (p - (d : ℤ)) :=
  compSmoothEquiv (fun _ ↦ 0) (𝟙 X) (terminal.from X) d p c

/-- Unfold composition with the smooth Gysin class of the structure morphism. -/
theorem capFundamental_compSmooth_eq (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) [RelativeDimension X.hom d] (p : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (𝟙 X) p) :
    capFundamental_compSmooth X d p c =
      compSmoothEquiv (fun _ ↦ 0) (𝟙 X) (terminal.from X) d p c := sorry

/-- The grading identity comparing the identity-square cap of the inverse class with the
over-`X` intersection product. -/
theorem capFundamentalEquiv_symm_cap_degree (d : ℕ) (p n : ℤ) :
    (d : ℤ) - p + n - d = n - p := sorry

/-- The second projection of the identity pullback `Y ×_X X → Y` is proper. -/
instance instProper_pullbackSnd_id {X Y : SchemeOverField k} (fY : Y ⟶ X) :
    IsProper (pullback.snd (𝟙 X) fY).left := sorry

/-- The identity of the underlying scheme of `X` is locally of finite type. -/
instance instLocallyOfFiniteType_id_left (X : SchemeOverField k) :
    LocallyOfFiniteType (𝟙 X.left) := sorry

/-- The inverse identification sends a Chow class `alpha` to the operational class whose
cap along a locally finite-type map `Y ⟶ X` is the over-`X` intersection product with
`alpha`. -/
theorem capFundamentalEquiv_symm_cap (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) [RelativeDimension X.hom d]
    [IsFiniteLocallyFreeOfRank d (conormalSheaf (ChowGroup.diagonal X).left)]
    (D : ChowGroup.DiagonalSpecialization X d) (p : ℤ)
    (alpha : RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p))
    {Y : SchemeOverField k} (fY : Y ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType fY.left]
    (n : ℤ) (beta : RelativeChow (fun _ ↦ 0) Y n) :
    ((capFundamentalEquiv X d p).symm alpha).cap fY (𝟙 Y) fY
        IsPullback.of_id_snd n beta =
      castRelativeDegree (fun _ ↦ 0) (capFundamentalEquiv_symm_cap_degree d p n)
        (ChowGroup.map (fun _ ↦ 0) (pullback (𝟙 X) fY) Y
          (pullback.snd (𝟙 X) fY) ((d : ℤ) - p + n - d)
          (ChowGroup.intersectionProductOver X (𝟙 X) fY d D alpha beta)) := sorry

end BivariantClass

end AlgebraicGeometry
