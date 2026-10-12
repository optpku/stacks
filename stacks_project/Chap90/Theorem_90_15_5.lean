/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.«90_15_0_1»
public import stacks_project.Chap90.«90_15_0_2»
public import stacks_project.Chap90.Example_90_15_3_Quotient
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Lemma_90_3_8_Pullback

/-!
# Miniversal formal objects with bijective differential

A predeformation category always satisfies
(miniversal + `BijectiveDifferential`) ⇒ (S1)+(S2)+finite-dimensional `tangentSpace` ⇒
(exists miniversal + `BijectiveDifferentialOnOrbits`). If `k / residueImage Λ k` is
separable, then `Derivation Λ k k` vanishes and the three conditions are equivalent.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ArtinianLocalAlgCat
open TrivSqZeroExt

universe u

namespace ArtinianLocalAlgCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Residue-field identification of `k[ε] ×_k k[ε]` with `k`, via the first projection
and the pair of inclusions of `k` into `k[ε]`. -/
noncomputable def dualNumberSelfPullbackResidueFieldIso :
    IsLocalRing.ResidueField
        (AlgHom.pullback (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    { toFun z :=
        (dualNumber Λ k).residueFieldIso
          (IsLocalRing.residue _
            (AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom
              (Quotient.out z)))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
    { toFun x :=
        IsLocalRing.residue _
          ⟨(((inlAlgHom k k k).restrictScalars Λ) x,
            ((inlAlgHom k k k).restrictScalars Λ) x),
            rfl⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
    sorry sorry

/-- The forward map of `dualNumberSelfPullbackResidueFieldIso` sends a residue class to the
residue identification of its first dual-number component. -/
theorem dualNumberSelfPullbackResidueFieldIso_apply
    (z : IsLocalRing.ResidueField
      (AlgHom.pullback (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom)) :
    dualNumberSelfPullbackResidueFieldIso Λ k z =
      (dualNumber Λ k).residueFieldIso
        (IsLocalRing.residue _
          (AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom
            (Quotient.out z))) := sorry

/-- The fibre product `k[ε] ×_k k[ε]` in `C_Λ`. -/
noncomputable def dualNumberSelfPullback : ArtinianLocalAlgCat Λ k :=
  of (AlgHom.pullback (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom)
    (dualNumberSelfPullbackResidueFieldIso Λ k)

/-- `dualNumberSelfPullback` is the algebra pullback of two coefficient projections. -/
theorem dualNumberSelfPullback_carrier :
    (dualNumberSelfPullback Λ k).carrier =
      AlgHom.pullback (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom := sorry

/-- The first projection `k[ε] ×_k k[ε] ⟶ k[ε]`. -/
noncomputable def dualNumberSelfPullbackFst :
    dualNumberSelfPullback Λ k ⟶ dualNumber Λ k where
  hom := AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The second projection `k[ε] ×_k k[ε] ⟶ k[ε]`. -/
noncomputable def dualNumberSelfPullbackSnd :
    dualNumberSelfPullback Λ k ⟶ dualNumber Λ k where
  hom := AlgHom.pullbackSnd (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberSelfPullbackFst` is the first algebra projection. -/
theorem dualNumberSelfPullbackFst_hom :
    (dualNumberSelfPullbackFst Λ k).hom =
      AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom := sorry

/-- The underlying algebra map of `dualNumberSelfPullbackSnd` is the second algebra projection. -/
theorem dualNumberSelfPullbackSnd_hom :
    (dualNumberSelfPullbackSnd Λ k).hom =
      AlgHom.pullbackSnd (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom := sorry

/-- The sum map `k[ε] ×_k k[ε] ⟶ k[ε]`, sending a pair `a+bε`, `a'+b'ε` to
`a+a'+(b+b')ε` (equivalently `a+(b+b')ε` on the fibre product). -/
noncomputable def dualNumberSum : dualNumberSelfPullback Λ k ⟶ dualNumber Λ k where
  hom :=
    { toFun := fun p ↦
        let fstP :=
          AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom p
        let sndP :=
          AlgHom.pullbackSnd (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom p
        ⟨fstP.fst, fstP.snd + sndP.snd⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberSum` adds the infinitesimal coefficients. -/
theorem dualNumberSum_hom (x : (dualNumberSelfPullback Λ k).carrier) :
    (dualNumberSum Λ k).hom x =
      let fstP :=
        AlgHom.pullbackFst (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom x
      let sndP :=
        AlgHom.pullbackSnd (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).hom x
      ⟨fstP.fst, fstP.snd + sndP.snd⟩ := sorry

/-- Scaling of dual numbers in the `ε`-direction by `r : k`, i.e. `a+bε ↦ a+(r • b)ε`. -/
def dualNumberSMul (r : k) : dualNumber Λ k ⟶ dualNumber Λ k where
  hom := (map (LinearMap.lsmul k k r)).restrictScalars Λ
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberSMul Λ k r` is `TrivSqZeroExt.map` of scaling. -/
theorem dualNumberSMul_hom (r : k) :
    (dualNumberSMul Λ k r).hom = (map (LinearMap.lsmul k k r)).restrictScalars Λ := sorry

/-- The canonical inclusion `k ⟶ k[ε]`, `a ↦ a`. -/
def residueToDualNumber : residue Λ k ⟶ dualNumber Λ k where
  hom := (inlAlgHom k k k).restrictScalars Λ
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `residueToDualNumber` is the dual-number inclusion. -/
theorem residueToDualNumber_hom :
    (residueToDualNumber Λ k).hom = (inlAlgHom k k k).restrictScalars Λ := sorry

/-- The canonical map `k ⟶ k[ε] ×_k k[ε]` sending `a` to the pair of inclusions. -/
noncomputable def residueToDualNumberSelfPullback :
    residue Λ k ⟶ dualNumberSelfPullback Λ k where
  hom :=
    { toFun := fun a ↦
        ⟨((residueToDualNumber Λ k).hom a, (residueToDualNumber Λ k).hom a), rfl⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `residueToDualNumberSelfPullback` pairs the two inclusions. -/
theorem residueToDualNumberSelfPullback_hom (a : (residue Λ k).carrier) :
    (residueToDualNumberSelfPullback Λ k).hom a =
      ⟨((residueToDualNumber Λ k).hom a, (residueToDualNumber Λ k).hom a), rfl⟩ := sorry

end ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- If `k / residueImage Λ k` is separable, then `Derivation Λ k k` is a subsingleton. -/
theorem subsingleton_derivation_of_isSeparable
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    Subsingleton (Derivation Λ k k) := sorry

namespace CategoryTheory.Functor

/-- Theorem 90.15.5 (1): if `p` is a predeformation category and `ξ` is a minimal
versal formal object of `p` such that `FormalObject.BijectiveDifferential ξ` holds,
then every cospan in `p` with a surjective second leg completes to a commutative
square whose image is a pullback. -/
@[stacks 06IX]
theorem hasSchlessingerS1_of_isMinimalVersal_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsMinimalVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective (p.map f2).hom →
        ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

/-- Theorem 90.15.5 (2): if `p` is a predeformation category and `ξ` is a minimal
versal formal object of `p` such that `FormalObject.BijectiveDifferential ξ` holds,
then `p` satisfies Schlessinger's condition (S2). -/
@[stacks 06IX]
theorem hasSchlessingerS2_of_isMinimalVersal_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsMinimalVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    HasSchlessingerS2 p := sorry

/-- Inverse of `FormalObject.differential ξ`, as an equivalence `tangentSpace p ≃
Derivation Λ ξ.base.carrier k` obtained from `FormalObject.BijectiveDifferential`. -/
noncomputable def tangentSpaceEquivDerivation
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) :
    tangentSpace p ≃ Derivation Λ ξ.base.carrier k :=
  (Equiv.ofBijective (FormalObject.differential ξ) h).symm

/-- `tangentSpaceEquivDerivation` inverts `FormalObject.differential`. -/
theorem tangentSpaceEquivDerivation_symm_apply
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ)
    (D : Derivation Λ ξ.base.carrier k) :
    (tangentSpaceEquivDerivation ξ h).symm D = FormalObject.differential ξ D := sorry

/-- The fibre over `k` of a predeformation category has a unique isomorphism class. -/
noncomputable instance instUnique_fiberIsoClass_residue [IsPredeformationCategory p] :
    Unique ((fiberIsoClassFunctor p).obj (residue Λ k)) where
  default :=
    Quotient.mk'' (Classical.choice IsPredeformationCategory.nonempty_residueFiber)
  uniq := sorry

/-- Images of a class over `k[ε] ×_k k[ε]` under the two projections agree after mapping to `k`. -/
theorem tangentSpacePullbackComparison_mem [IsPredeformationCategory p]
    (y : (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k)) :
    (fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)
        ((fiberIsoClassFunctor p).map (dualNumberSelfPullbackFst Λ k) y) =
      (fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)
        ((fiberIsoClassFunctor p).map (dualNumberSelfPullbackSnd Λ k) y) := sorry

/-- The comparison sending an isomorphism class over `k[ε] ×_k k[ε]` to the matching pair of
classes over `k[ε]`. -/
noncomputable def tangentSpacePullbackComparison [IsPredeformationCategory p] :
    (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
      Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
        ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)) :=
  fun y ↦
    ⟨((fiberIsoClassFunctor p).map (dualNumberSelfPullbackFst Λ k) y,
        (fiberIsoClassFunctor p).map (dualNumberSelfPullbackSnd Λ k) y),
      tangentSpacePullbackComparison_mem y⟩

/-- The pair of projections of `tangentSpacePullbackComparison y` recovers the two
pushforwards of `y`. -/
theorem tangentSpacePullbackComparison_spec [IsPredeformationCategory p]
    (y : (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k)) :
    (tangentSpacePullbackComparison y).val =
      ((fiberIsoClassFunctor p).map (dualNumberSelfPullbackFst Λ k) y,
        (fiberIsoClassFunctor p).map (dualNumberSelfPullbackSnd Λ k) y) := sorry

/-- Under (S2), the dual-number fibre-product comparison on isomorphism classes is bijective. -/
theorem bijective_tangentSpacePullbackComparison
    [IsPredeformationCategory p] [HasSchlessingerS2 p] :
    Function.Bijective
      (tangentSpacePullbackComparison :
        (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
          Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
            ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))) := sorry

/-- The (S2) comparison equivalence obtained from a given bijectivity proof. -/
noncomputable def tangentSpacePullbackEquiv [IsPredeformationCategory p]
    (h : Function.Bijective
      (tangentSpacePullbackComparison :
        (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
          Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
            ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)))) :
    (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) ≃
      Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
        ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)) :=
  Equiv.ofBijective tangentSpacePullbackComparison h

/-- `tangentSpacePullbackEquiv` is `Equiv.ofBijective` of the comparison map. -/
theorem tangentSpacePullbackEquiv_apply [IsPredeformationCategory p]
    (h : Function.Bijective
      (tangentSpacePullbackComparison :
        (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
          Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
            ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))))
    (y : (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k)) :
    tangentSpacePullbackEquiv h y = tangentSpacePullbackComparison y := sorry

/-- Two tangent vectors determine a matching pair over `k`, using uniqueness of the residue
fibre class. -/
theorem tangentSpaceAddPair_mem [IsPredeformationCategory p] (x y : tangentSpace p) :
    (fiberIsoClassFunctor p).map (dualNumberToResidue Λ k) x =
      (fiberIsoClassFunctor p).map (dualNumberToResidue Λ k) y := sorry

/-- The matching pair of tangent vectors over the dual-number cospan `k[ε] ⟶ k ← k[ε]`. -/
noncomputable def tangentSpaceAddPair [IsPredeformationCategory p] (x y : tangentSpace p) :
    Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
      ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)) :=
  ⟨(x, y), tangentSpaceAddPair_mem x y⟩

/-- `tangentSpaceAddPair x y` is the pair `(x, y)` of matching dual-number classes. -/
theorem tangentSpaceAddPair_spec [IsPredeformationCategory p] (x y : tangentSpace p) :
    (tangentSpaceAddPair x y).val = (x, y) := sorry

/-- The dual-number pullback fibre has an isomorphism class, namely the pushforward of the
unique residue class. -/
noncomputable instance instNonempty_fiberIsoClass_dualNumberSelfPullback
    [IsPredeformationCategory p] :
    Nonempty ((fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k)) :=
  ⟨(fiberIsoClassFunctor p).map (residueToDualNumberSelfPullback Λ k) default⟩

/-- Addition on `tangentSpace p` via the (S2) comparison along `k[ε] ×_k k[ε]` and the sum map,
using a supplied bijectivity proof of `tangentSpacePullbackComparison`. -/
noncomputable def addTangentSpace [IsPredeformationCategory p]
    (h : Function.Bijective
      (tangentSpacePullbackComparison :
        (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
          Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
            ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))))
    (x y : tangentSpace p) : tangentSpace p :=
  (fiberIsoClassFunctor p).map (dualNumberSum Λ k)
    ((tangentSpacePullbackEquiv h).symm (tangentSpaceAddPair x y))

/-- Scalar multiplication on `tangentSpace p` by dual-number scaling of `ε`. -/
noncomputable def smulTangentSpace [IsPredeformationCategory p]
    (r : k) (x : tangentSpace p) : tangentSpace p :=
  (fiberIsoClassFunctor p).map (dualNumberSMul Λ k r) x

/-- Zero of `tangentSpace p`, as the image of the unique residue class along `k ⟶ k[ε]`. -/
noncomputable def zeroTangentSpace [IsPredeformationCategory p] : tangentSpace p :=
  (fiberIsoClassFunctor p).map (residueToDualNumber Λ k) default

/-- `zeroTangentSpace` is the pushforward of the unique residue class along `k ⟶ k[ε]`. -/
theorem zeroTangentSpace_spec [IsPredeformationCategory p] :
    zeroTangentSpace =
      (fiberIsoClassFunctor p).map (residueToDualNumber Λ k) default := sorry

/-- `addTangentSpace` is pushforward of the inverted matching pair along `dualNumberSum`. -/
theorem addTangentSpace_spec [IsPredeformationCategory p]
    (h : Function.Bijective
      (tangentSpacePullbackComparison :
        (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
          Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
            ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))))
    (x y : tangentSpace p) :
    addTangentSpace h x y =
      (fiberIsoClassFunctor p).map (dualNumberSum Λ k)
        ((tangentSpacePullbackEquiv h).symm (tangentSpaceAddPair x y)) := sorry

/-- `smulTangentSpace r` is pushforward along `dualNumberSMul Λ k r`. -/
theorem smulTangentSpace_spec [IsPredeformationCategory p] (r : k) (x : tangentSpace p) :
    smulTangentSpace r x = (fiberIsoClassFunctor p).map (dualNumberSMul Λ k r) x := sorry

/-- Addition on `tangentSpace p`, using `Function.invFun` of the comparison rather than a
bijectivity proof. -/
noncomputable instance instAdd_tangentSpace [IsPredeformationCategory p] [HasSchlessingerS2 p] :
    Add (tangentSpace p) where
  add x y :=
    (fiberIsoClassFunctor p).map (dualNumberSum Λ k)
      (Function.invFun
        (tangentSpacePullbackComparison :
          (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
            Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
              ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k)))
        (tangentSpaceAddPair x y))

/-- Zero on `tangentSpace p`. -/
noncomputable instance instZero_tangentSpace [IsPredeformationCategory p] :
    Zero (tangentSpace p) where
  zero := zeroTangentSpace

/-- Negation on `tangentSpace p`, as scaling by `-1`. -/
noncomputable instance instNeg_tangentSpace [IsPredeformationCategory p] :
    Neg (tangentSpace p) where
  neg x := smulTangentSpace (-1) x

/-- Scalar multiplication on `tangentSpace p`. -/
noncomputable instance instSMul_tangentSpace [IsPredeformationCategory p] :
    SMul k (tangentSpace p) where
  smul := smulTangentSpace

/-- The additive group structure on `tangentSpace p` induced by (S2). -/
noncomputable instance instAddCommGroup_tangentSpace
    [IsPredeformationCategory p] [HasSchlessingerS2 p] :
    AddCommGroup (tangentSpace p) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-module structure on `tangentSpace p` induced by (S2). -/
noncomputable instance instModule_tangentSpace
    [IsPredeformationCategory p] [HasSchlessingerS2 p] :
    Module k (tangentSpace p) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Instance addition agrees with `addTangentSpace` of a bijectivity proof of the comparison. -/
theorem add_eq_addTangentSpace [IsPredeformationCategory p] [HasSchlessingerS2 p]
    (h : Function.Bijective
      (tangentSpacePullbackComparison :
        (fiberIsoClassFunctor p).obj (dualNumberSelfPullback Λ k) →
          Types.PullbackObj ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))
            ((fiberIsoClassFunctor p).map (dualNumberToResidue Λ k))))
    (x y : tangentSpace p) :
    x + y = addTangentSpace h x y := sorry

/-- Theorem 90.15.5 (3): if `p` is a predeformation category satisfying (S2) and `ξ` is a
minimal versal formal object of `p` such that `FormalObject.BijectiveDifferential ξ` holds,
then `tangentSpace p` is finite-dimensional over `k` for `instModule_tangentSpace`. -/
@[stacks 06IX]
theorem finiteDimensional_tangentSpace_of_isMinimalVersal_bijectiveDifferential
    [IsPredeformationCategory p] [HasSchlessingerS2 p] (ξ : FormalObject p)
    [FormalObject.IsMinimalVersal ξ] (h : FormalObject.BijectiveDifferential ξ) :
    FiniteDimensional k (tangentSpace p) := sorry

end CategoryTheory.Functor

namespace FormalObject

/-- Theorem 90.15.5 (4): if `p` is a predeformation category satisfying Schlessinger's
condition (S1) in the diagram-completion form, condition (S2), and with
`Functor.tangentSpace p` finite-dimensional over `k`, then `p` has a minimal versal
formal object satisfying `BijectiveDifferentialOnOrbits`. -/
@[stacks 06IX]
theorem exists_isMinimalVersal_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS2 p]
    (h_s1 : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective (p.map f2).hom →
        ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2))
    [FiniteDimensional k (Functor.tangentSpace p)] :
    ∃ ξ : FormalObject p, IsMinimalVersal ξ ∧ BijectiveDifferentialOnOrbits ξ := sorry

/-- Theorem 90.15.5 (5): if `k / residueImage Λ k` is separable and `ξ` is a minimal
versal formal object of `p` satisfying `BijectiveDifferentialOnOrbits`, then
`BijectiveDifferential ξ` holds. -/
@[stacks 06IX]
theorem bijectiveDifferential_of_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] (ξ : FormalObject p)
    [IsMinimalVersal ξ] (h : BijectiveDifferentialOnOrbits ξ) :
    BijectiveDifferential ξ := sorry

/-- If `k / residueImage Λ k` is separable, then `BijectiveDifferential ξ` is equivalent
to `BijectiveDifferentialOnOrbits ξ` for any formal object `ξ` of `p`. -/
theorem bijectiveDifferential_iff_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] (ξ : FormalObject p) :
    BijectiveDifferential ξ ↔ BijectiveDifferentialOnOrbits ξ := sorry

/-- If `k / residueImage Λ k` is separable, then Schlessinger's conditions (S1) and
(S2) together with finite-dimensionality of `Functor.tangentSpace p` yield a minimal
versal formal object satisfying `BijectiveDifferential`. -/
theorem exists_isMinimalVersal_bijectiveDifferential
    [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS2 p]
    (h_s1 : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective (p.map f2).hom →
        ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2))
    [FiniteDimensional k (Functor.tangentSpace p)]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ∃ ξ : FormalObject p, IsMinimalVersal ξ ∧ BijectiveDifferential ξ := sorry

end FormalObject

