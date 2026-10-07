module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import stacks_project.Chap92.Lemma_92_4_2_Resolution
public import stacks_project.Chap92.Remark_92_5_5_Resolutions_Resolution
public import stacks_project.Chap92.«92_7_0_2_Triple»

/-!
# Functorial standard resolutions and the auxiliary algebra Q̄

For ring maps `A → B → C` with `B → C` injective, the degreewise functoriality map from
the standard resolution `P_•` of `B` over `A` to the standard resolution `Q_•` of `C` over
`A` makes each `Q_n` a polynomial algebra over `P_n`. The resulting pairs
`(P_n → B, Q_n → C)` assemble into a simplicial object of `PolynomialTriple A B C`, and
the tensors `Q̄_n = Q_n ⊗[P_n] B` form a simplicial polynomial `B`-algebra augmenting to
`C`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open Algebra
open Algebra.PolynomialSite
open RingedSite.Cotangent
open RingedSite.Cotangent.PolynomialTriple
open Under

noncomputable section

universe u

namespace Algebra.CotangentComplex

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The standard-resolution term `P_n` of `B` over `A`. -/
abbrev standardP (n : SimplexCategoryᵒᵖ) : Type u :=
  (standardAugmented A B).left.obj n

/-- Unfolding `standardP` recovers the corresponding term of `standardAugmented`. -/
theorem standardP_eq (n : SimplexCategoryᵒᵖ) :
    standardP A B n = (standardAugmented A B).left.obj n :=
  sorry

/-- The standard-resolution term `Q_n` of `C` over `A`. -/
abbrev standardQ (n : SimplexCategoryᵒᵖ) : Type u :=
  (standardAugmented A C).left.obj n

/-- Unfolding `standardQ` recovers the corresponding term of `standardAugmented`. -/
theorem standardQ_eq (n : SimplexCategoryᵒᵖ) :
    standardQ A C n = (standardAugmented A C).left.obj n :=
  sorry

/-- The morphism of under-objects induced by `B → C` over `A`. -/
def underHom : (CommRingCat.of A).mkUnder B ⟶ (CommRingCat.of A).mkUnder C :=
  Under.homMk (CommRingCat.ofHom (algebraMap B C)) sorry

/-- The underlying ring map of `underHom` is `algebraMap B C`. -/
theorem underHom_right :
    (underHom A B C).right = CommRingCat.ofHom (algebraMap B C) :=
  sorry

/-- The map of standard polynomial resolutions induced by `B → C`. -/
def standardFunctoriality : standardAugmented A B ⟶ standardAugmented A C :=
  (SimplicialObject.Augmented.whiskeringObj (Under (CommRingCat.of A))
      (CommAlgCat.{u} A) (commAlgCatEquivUnder (CommRingCat.of A)).inverse).map
    ((evaluation (CommRingCat.of A)).map (underHom A B C))

/-- Unfolding `standardFunctoriality` recovers whiskered `evaluation.map`. -/
theorem standardFunctoriality_eq :
    standardFunctoriality A B C =
      (SimplicialObject.Augmented.whiskeringObj (Under (CommRingCat.of A))
          (CommAlgCat.{u} A) (commAlgCatEquivUnder (CommRingCat.of A)).inverse).map
        ((evaluation (CommRingCat.of A)).map (underHom A B C)) :=
  sorry

/-- The degree-`n` functoriality map `P_n ⟶ Q_n`. -/
def functorialityApp (n : SimplexCategoryᵒᵖ) :
    (standardAugmented A B).left.obj n ⟶ (standardAugmented A C).left.obj n :=
  (standardFunctoriality A B C).left.app n

/-- Components of `functorialityApp` are the simplicial components of
`standardFunctoriality`. -/
theorem functorialityApp_eq (n : SimplexCategoryᵒᵖ) :
    functorialityApp A B C n = (standardFunctoriality A B C).left.app n :=
  sorry

/-- The `P_n`-algebra structure on `Q_n` induced by functoriality. -/
@[reducible] instance instAlgebraPQ (n : SimplexCategoryᵒᵖ) :
    Algebra (standardP A B n) (standardQ A C n) :=
  RingHom.toAlgebra (functorialityApp A B C n).hom.toRingHom

/-- Unfolding `instAlgebraPQ` recovers the underlying ring map of `functorialityApp`. -/
theorem instAlgebraPQ_eq (n : SimplexCategoryᵒᵖ) :
    instAlgebraPQ A B C n = RingHom.toAlgebra (functorialityApp A B C n).hom.toRingHom :=
  sorry

/-- The standard-resolution augmentation `P_n →ₐ[A] B`. -/
def toBAlg (n : SimplexCategoryᵒᵖ) : standardP A B n →ₐ[A] B :=
  ((standardHom A B).app n).hom

/-- Unfolding `toBAlg` recovers the corresponding component of `standardHom`. -/
theorem toBAlg_eq (n : SimplexCategoryᵒᵖ) :
    toBAlg A B n = ((standardHom A B).app n).hom :=
  sorry

/-- The `P_n`-algebra structure on `C` induced by `P_n → B → C`. -/
@[reducible] instance instAlgebraPC (n : SimplexCategoryᵒᵖ) :
    Algebra (standardP A B n) C :=
  algebraPCOf (toBAlg A B n)

/-- Unfolding `instAlgebraPC` recovers `algebraPCOf` of `toBAlg`. -/
theorem instAlgebraPC_eq (n : SimplexCategoryᵒᵖ) :
    instAlgebraPC A B C n = algebraPCOf (toBAlg A B n) :=
  sorry

/-- The underlying ring map of the standard-resolution augmentation `Q_n → C`. -/
def standardAugRingHom (n : SimplexCategoryᵒᵖ) : standardQ A C n →+* C :=
  ((standardHom A C).app n).hom.toRingHom

/-- Unfolding `standardAugRingHom` recovers the ring homomorphism of `standardHom`. -/
theorem standardAugRingHom_eq (n : SimplexCategoryᵒᵖ) :
    standardAugRingHom A C n = ((standardHom A C).app n).hom.toRingHom :=
  sorry

/-- The standard-resolution augmentation `Q_n → C`, as a `P_n`-algebra map. -/
def standardAugAlgHom (n : SimplexCategoryᵒᵖ) : standardQ A C n →ₐ[standardP A B n] C where
  toRingHom := standardAugRingHom A C n
  commutes' := sorry

/-- The underlying ring map of `standardAugAlgHom` is `standardAugRingHom`. -/
theorem standardAugAlgHom_toRingHom (n : SimplexCategoryᵒᵖ) :
    (standardAugAlgHom A B C n).toRingHom = standardAugRingHom A C n :=
  sorry

/-- If `B → C` is injective, then each standard-resolution term `Q_n` is a polynomial
algebra over `P_n`. -/
theorem isPolynomial_standardQ_over_standardP (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial (standardP A B n) (standardQ A C n) :=
  sorry

/-- The polynomial triple `(P_n → B, Q_n → C)` attached to the functorial standard
resolutions, using injectivity of `B → C` to obtain the polynomial algebra structure
`P_n → Q_n`. -/
def triple (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    PolynomialTriple A B C :=
  @PolynomialTriple.of A B C _ _ _ _ _ _ _ (standardP A B n) (standardQ A C n) _ _ _ _
    (standard_isPolynomial A B n)
    (isPolynomial_standardQ_over_standardP A B C n h_inj)
    (toBAlg A B n) (standardAugAlgHom A B C n)

/-- The first factor of `triple n h_inj` is the standard-resolution term `P_n`. -/
theorem triple_P (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    (triple A B C n h_inj).P = standardP A B n :=
  sorry

/-- The second factor of `triple n h_inj` is the standard-resolution term `Q_n`. -/
theorem triple_Q (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    (triple A B C n h_inj).Q = standardQ A C n :=
  sorry

/-- The morphism of triples induced by a simplicial operator. -/
def tripleMap {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (h_inj : Function.Injective (algebraMap B C)) :
    triple A B C n h_inj ⟶ triple A B C m h_inj where
  toP := ((standardAugmented A B).left.map φ).hom
  commB := sorry
  toQ := ((standardAugmented A C).left.map φ).hom.toRingHom
  commP := sorry
  commC := sorry

/-- Identity simplicial operators act as identity morphisms of triples. -/
theorem tripleMap_id (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    tripleMap A B C (𝟙 n) h_inj = 𝟙 (triple A B C n h_inj) :=
  sorry

/-- Composition of simplicial operators is preserved by `tripleMap`. -/
theorem tripleMap_comp {n m k : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (ψ : m ⟶ k)
    (h_inj : Function.Injective (algebraMap B C)) :
    tripleMap A B C (φ ≫ ψ) h_inj =
      tripleMap A B C φ h_inj ≫ tripleMap A B C ψ h_inj :=
  sorry

/-- The simplicial object of polynomial triples `(P_n → B, Q_n → C)`. -/
def tripleSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (PolynomialTriple A B C) where
  obj n := triple A B C n h_inj
  map φ := tripleMap A B C φ h_inj
  map_id n := tripleMap_id A B C n h_inj
  map_comp φ ψ := tripleMap_comp A B C φ ψ h_inj

/-- Degreewise, `tripleSimplicial` is `triple`. -/
theorem tripleSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (tripleSimplicial A B C h_inj).obj n = triple A B C n h_inj :=
  sorry

/-- The cosimplicial object of the site `C_{C/B/A}` associated to the functorial
standard resolutions. -/
def tripleCosimplicial (h_inj : Function.Injective (algebraMap B C)) :
    CosimplicialObject (site A B C) :=
  (tripleSimplicial A B C h_inj).rightOp

/-- Unpacking `tripleCosimplicial` in each degree recovers the opposite of the
corresponding triple. -/
theorem tripleCosimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategory) :
    (tripleCosimplicial A B C h_inj).obj n = Opposite.op (triple A B C (Opposite.op n) h_inj) :=
  sorry

/-- The polynomial `B`-algebra arrow `Q̄_n = Q_n ⊗[P_n] B ⟶ C`. -/
def barQOver (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    PolynomialOver B C :=
  tensorOverBase (triple A B C n h_inj)

/-- Unfolding `barQOver` recovers `tensorOverBase` of the corresponding triple. -/
theorem barQOver_eq (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    barQOver A B C n h_inj = tensorOverBase (triple A B C n h_inj) :=
  sorry

/-- The auxiliary algebra `Q̄_n = Q_n ⊗[P_n] B`. -/
abbrev barQ (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    Type u :=
  (barQOver A B C n h_inj).obj.left

/-- Unfolding `barQ` recovers the source of `barQOver`. -/
theorem barQ_eq (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    barQ A B C n h_inj = (barQOver A B C n h_inj).obj.left :=
  sorry

/-- Each `Q̄_n` is a polynomial `B`-algebra. -/
theorem isPolynomial_barQ (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial B (barQ A B C n h_inj) :=
  sorry

/-- The simplicial polynomial `B`-algebra `Q̄_•`. -/
def barQSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (CommAlgCat.{u} B) where
  obj n := (barQOver A B C n h_inj).obj.left
  map φ := ((forgetToOverB A B C).map (tripleMap A B C φ h_inj)).hom.left
  map_id n := sorry
  map_comp φ ψ := sorry

/-- Degreewise, `barQSimplicial` is the source of `barQOver`. -/
theorem barQSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (barQSimplicial A B C h_inj).obj n = (barQOver A B C n h_inj).obj.left :=
  sorry

/-- The augmentation `Q̄_• ⟶ C` of simplicial `B`-algebras. -/
def barQHom (h_inj : Function.Injective (algebraMap B C)) :
    barQSimplicial A B C h_inj ⟶
      (const (CommAlgCat.{u} B)).obj (CommAlgCat.of B C) where
  app n := (barQOver A B C n h_inj).obj.hom
  naturality _ _ _ := sorry

/-- Components of `barQHom` are the structure morphisms of `barQOver`. -/
theorem barQHom_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (barQHom A B C h_inj).app n = (barQOver A B C n h_inj).obj.hom :=
  sorry

/-- The auxiliary algebra `Q̄_•` is a polynomial simplicial resolution of `C` over `B`. -/
theorem isResolution_barQHom (h_inj : Function.Injective (algebraMap B C)) :
    IsResolution (barQHom A B C h_inj) :=
  sorry

/-- Being a resolution of `C` over `B` is equivalent to the degreewise polynomial
condition on `Q̄_n` together with the trivial Kan fibration condition on `barQHom`. -/
theorem isResolution_barQHom_iff (h_inj : Function.Injective (algebraMap B C)) :
    IsResolution (barQHom A B C h_inj) ↔
      (∀ n, IsPolynomial B ((barQSimplicial A B C h_inj).obj n)) ∧
        SSet.modelCategoryQuillen.I.rlp (underlyingSSetMap (barQHom A B C h_inj)) :=
  sorry

end Algebra.CotangentComplex
