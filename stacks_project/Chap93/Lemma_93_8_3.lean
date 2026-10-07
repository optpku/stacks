module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap90.Definition_90_12_1_TangentSpace
public import stacks_project.Chap91.Lemma_91_2_2
public import stacks_project.Chap93.Lemma_93_8_3_Deformation

/-!
# Tangent space and infinitesimal automorphisms of `Def_P`

In Example 93.8.1, `T Def_P` identifies with `Ext^1_P(NL_{P/k}, P)` and
`Inf(Def_P)` identifies with `Der_k(P, P)`.
-/

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt
open RingHom.SquareZeroExtension

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The ring map `id + ε D` on `P[ε]`. -/
def idAddEpsilonRingHom (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    DualNumber P →+* DualNumber P where
  toFun x := ⟨x.fst, x.snd + D x.fst⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The underlying function of `idAddEpsilonRingHom D` is `(a, b) ↦ (a, b + D a)`. -/
theorem idAddEpsilonRingHom_apply (P : Type u) [CommRing P] [Algebra k P]
    (D : Derivation k P P) (x : DualNumber P) :
    idAddEpsilonRingHom k P D x = ⟨x.fst, x.snd + D x.fst⟩ := sorry

/-- `id + ε D` as an endomorphism of the trivial deformation in `F`. -/
def idAddEpsilonHom (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    trivialDeformationObj Λ k P ⟶ trivialDeformationObj Λ k P :=
  Hom.of (𝟙 (dualNumber Λ k)) (idAddEpsilonRingHom k P D) sorry sorry

/-- The underlying algebra map of `idAddEpsilonHom D` is `idAddEpsilonRingHom D`. -/
theorem idAddEpsilonHom_toRingHom (P : Type u) [CommRing P] [Algebra k P]
    (D : Derivation k P P) :
    (idAddEpsilonHom Λ k P D).toRingHom = idAddEpsilonRingHom k P D := sorry

/-- `id + ε D` as an automorphism of the trivial deformation in the dual-number fibre of
`Def_P`. This is the comparison map `Der_k(P, P) → Inf(Def_P)`. -/
def infAutOfDerivation (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    Aut (trivialDeformationFiber Λ k P) where
  hom := ⟨Over.homMk (idAddEpsilonHom Λ k P D) sorry, sorry⟩
  inv := ⟨Over.homMk (idAddEpsilonHom Λ k P (-D)) sorry, sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The comparison `γ = id + ε D` sends addition of derivations to composition of
infinitesimal automorphisms. -/
theorem infAutOfDerivation_map_add (P : Type u) [CommRing P] [Algebra k P]
    (D E : Derivation k P P) :
    infAutOfDerivation Λ k P (D + E) =
      infAutOfDerivation Λ k P D * infAutOfDerivation Λ k P E := sorry

/-- The coefficient projection `k[ε] ⟶ k`, as a square-zero ring homomorphism. -/
def dualNumberProjRingHom : DualNumber k →+* k :=
  (fstHom k k k).toRingHom

/-- `dualNumberProjRingHom` is the first projection of `DualNumber k`. -/
theorem dualNumberProjRingHom_apply (x : DualNumber k) :
    dualNumberProjRingHom k x = x.fst := sorry

/-- The projection `k[ε] ⟶ k` is a square-zero extension. -/
instance instIsSquareZeroExtension_dualNumberProjRingHom :
    (dualNumberProjRingHom k).IsSquareZeroExtension :=
  ⟨sorry, sorry⟩

/-- The kernel map `c : I → P` of diagram 91.2.0.1 for the dual-number projection, sending
the second coefficient of a kernel element to `P` along `algebraMap k P`. -/
def kernelToAlgebra (P : Type u) [CommRing P] [Algebra k P] :
    KernelModule (dualNumberProjRingHom k) →ₗ[k] P where
  toFun x := algebraMap k P (val x).snd
  map_add' := sorry
  map_smul' := sorry

/-- `kernelToAlgebra` evaluates the second coefficient of a kernel dual number. -/
theorem kernelToAlgebra_apply (P : Type u) [CommRing P] [Algebra k P]
    (x : KernelModule (dualNumberProjRingHom k)) :
    kernelToAlgebra k P x = algebraMap k P (val x).snd := sorry

/-- The projection `P[ε] → P` is a square-zero extension. -/
instance instIsSquareZeroExtension_dualNumberFstRingHom
    (P : Type u) [CommRing P] [Algebra k P] :
    (dualNumberFstRingHom k P).IsSquareZeroExtension :=
  ⟨sorry, sorry⟩

/-- B-linear identification of `ker(P[ε] → P)` with `P`, via the second projection. -/
def kernelEquiv_fst (P : Type u) [CommRing P] [Algebra k P] :
    KernelModule (dualNumberFstRingHom k P) ≃ₗ[P] P where
  toFun x := (val x).snd
  invFun n := ⟨inr n, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- On a kernel element, `kernelEquiv_fst` is the second projection of `DualNumber P`. -/
theorem kernelEquiv_fst_apply (P : Type u) [CommRing P] [Algebra k P]
    (x : KernelModule (dualNumberFstRingHom k P)) :
    kernelEquiv_fst k P x = (val x).snd := sorry

/-- The trivial square-zero solution of diagram 91.2.0.1 with middle ring `P[ε]`. -/
def trivialSolution (P : Type u) [CommRing P] [Algebra k P] :
    @Solution (DualNumber k) k _ _ P _ _ (dualNumberProjRingHom k) _ P _ _ _
      (kernelToAlgebra k P) _ :=
  Solution.of (dualNumberProjRingHom k) (kernelToAlgebra k P)
    (dualNumberRingHom Λ k P) (dualNumberFstRingHom k P) sorry
    (kernelEquiv_fst k P) sorry

/-- The carrier of the trivial solution is `DualNumber P`. -/
theorem trivialSolution_carrier (P : Type u) [CommRing P] [Algebra k P] :
    (trivialSolution Λ k P).carrier = DualNumber P := sorry

/-- Package a square-zero solution as a dual-number fibre object of `Def_P`. -/
def ofSolution (P : Type u) [CommRing P] [Algebra k P]
    (S : @Solution (DualNumber k) k _ _ P _ _ (dualNumberProjRingHom k) _ P _ _ _
      (kernelToAlgebra k P) _) :
    Functor.tangentSpace (deformationForget Λ k P) :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  -- Local instance justification (proof-local temporary data): the DualNumber-algebra structure on a solution carrier is determined by `S.fromA'` and cannot be a global instance.
  letI : Algebra (dualNumber Λ k).carrier S.carrier := S.fromA'.toAlgebra
  -- Local instance justification (proof-local temporary data): flatness of a solution carrier over k[ε] is a law of this particular solution, not a global instance.
  letI : Module.Flat (dualNumber Λ k).carrier S.carrier := sorry
  let obj := of (dualNumber Λ k) S.carrier
  let hom : obj ⟶ ofResidue Λ k P :=
    Hom.of (dualNumberToResidue Λ k) S.toB sorry sorry
  tangentSpace.mk (deformationForget Λ k P)
    (Fiber.mk (sorry : (deformationForget Λ k P).obj (Over.mk hom) = dualNumber Λ k))

/-- Fitting maps of the identity connecting diagram identify tangent classes of solutions. -/
theorem ofSolution_iso_iff (P : Type u) [CommRing P] [Algebra k P]
    (S T : @Solution (DualNumber k) k _ _ P _ _ (dualNumberProjRingHom k) _ P _ _ _
      (kernelToAlgebra k P) _) :
    ofSolution Λ k P S = ofSolution Λ k P T ↔ Nonempty (FittingMap (compare S T)) := sorry

/-- Send an isomorphism class of square-zero solutions to its class in `T Def_P`. -/
def ofIsoClass (P : Type u) [CommRing P] [Algebra k P] :
    IsoClass (dualNumberProjRingHom k) P (kernelToAlgebra k P) →
      Functor.tangentSpace (deformationForget Λ k P) :=
  Quotient.lift (ofSolution Λ k P) sorry

/-- `ofIsoClass` sends the class of a solution to `ofSolution`. -/
theorem ofIsoClass_mk (P : Type u) [CommRing P] [Algebra k P]
    (S : @Solution (DualNumber k) k _ _ P _ _ (dualNumberProjRingHom k) _ P _ _ _
      (kernelToAlgebra k P) _) :
    ofIsoClass Λ k P (isoClassMk S) = ofSolution Λ k P S := sorry

/-- The comparison sending a class in `Ext^1_P(NL_{P/k}, P)` to its image in `T Def_P`,
via the based chart `isoClassEquiv` of Lemma 91.2.2 at the trivial solution `P[ε]`. -/
def ofExtClass (P : Type u) [CommRing P] [Algebra k P]
    (ξ : extOneNaiveCotangent k P P) :
    Functor.tangentSpace (deformationForget Λ k P) :=
  ofIsoClass Λ k P (isoClassEquiv (trivialSolution Λ k P) ξ)

/-- The zero Ext class is sent to the class of the trivial dual-number fibre of `Def_P`. -/
theorem ofExtClass_zero (P : Type u) [CommRing P] [Algebra k P] :
    ofExtClass Λ k P 0 =
      tangentSpace.mk (deformationForget Λ k P) (trivialDeformationFiber Λ k P) := sorry

/-- Lemma 93.8.3 (1)
In Example 93.8.1 let P be a k-algebra. Then T Def_P equals Ext^1_P(NL_{P/k}, P),
as bijectivity of ofExtClass from the source model extOneNaiveCotangent k P P. -/
@[stacks 0DY3]
theorem ofExtClass_bijective (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (ofExtClass Λ k P) := sorry

/-- Lemma 93.8.3 (2)
In Example 93.8.1 let P be a k-algebra. Then Inf(Def_P) equals Der_k(P, P),
as bijectivity of infAutOfDerivation. -/
@[stacks 0DY3]
theorem infAutOfDerivation_bijective (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (infAutOfDerivation Λ k P) := sorry

end FlatAlgebraCat
