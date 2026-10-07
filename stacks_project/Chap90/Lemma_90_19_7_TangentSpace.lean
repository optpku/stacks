module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Module.Basic
public import stacks_project.Chap90.Definition_90_19_2_DualNumber
public import stacks_project.Chap90.Lemma_90_10_7_Pullback
public import stacks_project.Chap90.Lemma_90_12_2_SquareZero
public import stacks_project.Chap90.Lemma_90_19_6

/-!
# Identity-tangent space of an automorphism functor

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids, the identity-tangent
space `T_id Aut(x)` is the fibre of `autFunctor p x` over `A → k` inside the
automorphisms of the selected pushforward along `A → k[ε]`. Under (RS) this fibre
carries the `k`-module structure of Lemma 90.11.8, with addition induced by the
sum map on `k[ε] ×_k k[ε]` and scalar multiplication by `ε ↦ r·ε`.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Limits
open ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace ArtinianLocalAlgCat

/-- The object `A → k` of `Under A`, i.e. the canonical `C_A`-object given by `toResidue`. -/
def residueUnder (A : ArtinianLocalAlgCat Λ k) : Under A :=
  Under.mk (toResidue A)

/-- The structure map of `residueUnder A` is `toResidue A`. -/
theorem residueUnder_hom (A : ArtinianLocalAlgCat Λ k) :
    (residueUnder A).hom = toResidue A := sorry

/-- The object `A → k[ε]` of `Under A`, obtained by composing `toResidue` with
`residueToDualNumber`. -/
def dualNumberUnder (A : ArtinianLocalAlgCat Λ k) : Under A :=
  Under.mk (toResidue A ≫ residueToDualNumber Λ k)

/-- The structure map of `dualNumberUnder A` is `toResidue A ≫ residueToDualNumber`. -/
theorem dualNumberUnder_hom (A : ArtinianLocalAlgCat Λ k) :
    (dualNumberUnder A).hom = toResidue A ≫ residueToDualNumber Λ k := sorry

/-- Triangle identity for the dual-number restriction of an `Under A`-object. -/
theorem dualNumberToResidueUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ residueToDualNumber Λ k) ≫ dualNumberToResidue Λ k = toResidue A := sorry

/-- The restriction morphism `(A → k[ε]) ⟶ (A → k)` in `Under A`. -/
def dualNumberToResidueUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberUnder A ⟶ residueUnder A :=
  Under.homMk (dualNumberToResidue Λ k) (dualNumberToResidueUnder_w A)

/-- The underlying algebra map of `dualNumberToResidueUnder` is `dualNumberToResidue`. -/
theorem dualNumberToResidueUnder_right (A : ArtinianLocalAlgCat Λ k) :
    (dualNumberToResidueUnder A).right = dualNumberToResidue Λ k := sorry

/-- The dual-number restriction in `Under A` is surjective on underlying algebra maps. -/
theorem dualNumberToResidueUnder_surjective (A : ArtinianLocalAlgCat Λ k) :
    Function.Surjective (dualNumberToResidueUnder A).right.hom := sorry

/-- The unique structure map `k → k[ε] ×_k k[ε]`, as the composite of `residueToDualNumber`
with the canonical section of the first projection. -/
def dualNumberPullbackFromResidue :
    residue Λ k ⟶ dualNumberPullback (dualNumber Λ k) :=
  residueToDualNumber Λ k ≫ dualNumberPullbackSection (dualNumber Λ k)

/-- `dualNumberPullbackFromResidue` is the section of `dualNumberPullbackFst` after
`residueToDualNumber`. -/
theorem dualNumberPullbackFromResidue_comp_fst :
    dualNumberPullbackFromResidue ≫ dualNumberPullbackFst (dualNumber Λ k) =
      residueToDualNumber Λ k := sorry

/-- The object `A → k[ε] ×_k k[ε]` of `Under A`. -/
def dualNumberPullbackUnder (A : ArtinianLocalAlgCat Λ k) : Under A :=
  Under.mk (toResidue A ≫ dualNumberPullbackFromResidue)

/-- The structure map of `dualNumberPullbackUnder A` factors through
`dualNumberPullbackFromResidue`. -/
theorem dualNumberPullbackUnder_hom (A : ArtinianLocalAlgCat Λ k) :
    (dualNumberPullbackUnder A).hom = toResidue A ≫ dualNumberPullbackFromResidue := sorry

/-- Triangle identity for the first projection of `k[ε] ×_k k[ε]` in `Under A`. -/
theorem dualNumberPullbackFstUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ dualNumberPullbackFromResidue) ≫
        dualNumberPullbackFst (dualNumber Λ k) =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- The first projection `(A → k[ε] ×_k k[ε]) ⟶ (A → k[ε])` in `Under A`. -/
def dualNumberPullbackFstUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberPullbackUnder A ⟶ dualNumberUnder A :=
  Under.homMk (dualNumberPullbackFst (dualNumber Λ k)) (dualNumberPullbackFstUnder_w A)

/-- Triangle identity for the second projection of `k[ε] ×_k k[ε]` in `Under A`. -/
theorem dualNumberPullbackSndUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ dualNumberPullbackFromResidue) ≫
        dualNumberPullbackSnd (dualNumber Λ k) =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- The second projection `(A → k[ε] ×_k k[ε]) ⟶ (A → k[ε])` in `Under A`. -/
def dualNumberPullbackSndUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberPullbackUnder A ⟶ dualNumberUnder A :=
  Under.homMk (dualNumberPullbackSnd (dualNumber Λ k)) (dualNumberPullbackSndUnder_w A)

/-- Triangle identity for the sum map of `k[ε] ×_k k[ε]` in `Under A`. -/
theorem dualNumberSumUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ dualNumberPullbackFromResidue) ≫ dualNumberSum =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- The sum morphism `(A → k[ε] ×_k k[ε]) ⟶ (A → k[ε])` in `Under A`. -/
def dualNumberSumUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberPullbackUnder A ⟶ dualNumberUnder A :=
  Under.homMk dualNumberSum (dualNumberSumUnder_w A)

/-- Triangle identity for dual-number scaling in `Under A`. -/
theorem dualNumberSMulUnder_w (A : ArtinianLocalAlgCat Λ k) (r : k) :
    (toResidue A ≫ residueToDualNumber Λ k) ≫ dualNumberSMul Λ k r =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- Scaling by `r : k` as an endomorphism of `A → k[ε]` in `Under A`. -/
def dualNumberSMulUnder (A : ArtinianLocalAlgCat Λ k) (r : k) :
    dualNumberUnder A ⟶ dualNumberUnder A :=
  Under.homMk (dualNumberSMul Λ k r) (dualNumberSMulUnder_w A r)

/-- The dual-number fibre-product square, lifted to `Under A`. -/
theorem isPullback_dualNumberUnder (A : ArtinianLocalAlgCat Λ k) :
    IsPullback (dualNumberPullbackFstUnder A) (dualNumberPullbackSndUnder A)
      (dualNumberToResidueUnder A) (dualNumberToResidueUnder A) := sorry

end ArtinianLocalAlgCat

namespace CategoryTheory.Functor

open Fiber Chosen ArtinianLocalAlgCat

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- The selected dual-number pushforward of `x`, i.e. the fibre object
`(A → k[ε])_* x` whose automorphisms carry `T_id Aut(x)`. -/
abbrev idTangentSpaceObj [p.op.IsFibered] (x : F) : p.Fiber (dualNumber Λ k) :=
  pushforwardObj p (toResidue (p.obj x) ≫ residueToDualNumber Λ k) (ofObj p x)

/-- `idTangentSpaceObj` is the selected pushforward along `dualNumberUnder`. -/
theorem idTangentSpaceObj_eq [p.op.IsFibered] (x : F) :
    idTangentSpaceObj p x =
      pushforwardObj p (dualNumberUnder (p.obj x)).hom (ofObj p x) := sorry

/-- The identity-tangent space `T_id Aut(x)` is the fibre of `autFunctor p x` over
`A → k` inside `Aut ((A → k[ε])_* x)`. -/
def idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    Subgroup (Aut (idTangentSpaceObj p x)) where
  carrier :=
    {α | pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α =
      (1 : Aut (pushforwardObj p (toResidue (p.obj x)) (ofObj p x)))}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-- Membership in `idTangentSpace` is the identity-fibre condition for
`autFunctor.map` along `dualNumberToResidueUnder`. -/
theorem mem_idTangentSpace [IsFibered.InGroupoids p.op] (x : F)
    (α : Aut (idTangentSpaceObj p x)) :
    α ∈ idTangentSpace p x ↔
      pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α =
        (1 : Aut (pushforwardObj p (toResidue (p.obj x)) (ofObj p x))) := sorry

/-- The underlying set of `idTangentSpace` is the identity fibre of `autFunctor`. -/
theorem idTangentSpace_def [IsFibered.InGroupoids p.op] (x : F) :
    (idTangentSpace p x : Set (Aut (idTangentSpaceObj p x))) =
      {α | pushforwardAut p (dualNumberToResidueUnder (p.obj x)) (ofObj p x) α =
        (1 : Aut (pushforwardObj p (toResidue (p.obj x)) (ofObj p x)))} := sorry

/-- A matching pair of identity-tangent automorphisms, as an element of the type
pullback of the two dual-number restrictions. -/
def idTangentSpaceAddPair [IsFibered.InGroupoids p.op] {x : F}
    (α β : idTangentSpace p x) :
    Types.PullbackObj
      ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x)))
      ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x))) :=
  ⟨⟨α.val, β.val⟩, sorry⟩

/-- The (RS) comparison equivalence for the dual-number square in `Under (p.obj x)`. -/
def idTangentSpaceAddEquiv [HasRimSchlessinger p] (x : F) :
    (autFunctor p x).obj (dualNumberPullbackUnder (p.obj x)) ≃
      Types.PullbackObj
        ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x)))
        ((autFunctor p x).map (dualNumberToResidueUnder (p.obj x))) :=
  Equiv.ofBijective
    (autFunctorComparison p x
      (dualNumberToResidueUnder (p.obj x)) (dualNumberToResidueUnder (p.obj x))
      (dualNumberPullbackFstUnder (p.obj x)) (dualNumberPullbackSndUnder (p.obj x))
      (isPullback_dualNumberUnder (p.obj x)))
    (HasRimSchlessinger.autFunctorComparison_bijective p x
      (dualNumberToResidueUnder (p.obj x)) (dualNumberToResidueUnder (p.obj x))
      (dualNumberPullbackFstUnder (p.obj x)) (dualNumberPullbackSndUnder (p.obj x))
      (isPullback_dualNumberUnder (p.obj x))
      (dualNumberToResidueUnder_surjective (p.obj x)))

/-- Addition of identity-tangent automorphisms, via the (RS) inverse and
`dualNumberSumUnder`. -/
def idTangentSpaceAdd [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) : idTangentSpace p x :=
  ⟨(autFunctor p x).map (dualNumberSumUnder (p.obj x))
      ((idTangentSpaceAddEquiv p x).symm (idTangentSpaceAddPair p α β)), sorry⟩

/-- `idTangentSpaceAdd` applies `autFunctor.map dualNumberSumUnder` to the (RS) inverse
of the matching pair. -/
theorem idTangentSpaceAdd_spec [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) :
    (idTangentSpaceAdd p α β).val =
      (autFunctor p x).map (dualNumberSumUnder (p.obj x))
        ((idTangentSpaceAddEquiv p x).symm (idTangentSpaceAddPair p α β)) := sorry

/-- Scalar multiplication of identity-tangent automorphisms by dual-number scaling. -/
def idTangentSpaceSMul [IsFibered.InGroupoids p.op] {x : F}
    (r : k) (α : idTangentSpace p x) : idTangentSpace p x :=
  ⟨(autFunctor p x).map (dualNumberSMulUnder (p.obj x) r) α.val, sorry⟩

/-- `idTangentSpaceSMul r α` is `autFunctor.map` of `dualNumberSMulUnder r`. -/
theorem idTangentSpaceSMul_spec [IsFibered.InGroupoids p.op] {x : F}
    (r : k) (α : idTangentSpace p x) :
    (idTangentSpaceSMul p r α).val =
      (autFunctor p x).map (dualNumberSMulUnder (p.obj x) r) α.val := sorry

/-- Zero in the identity-tangent space is the identity automorphism. -/
instance instZero_idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    Zero (idTangentSpace p x) where
  zero := 1

/-- The additive zero of `idTangentSpace` is the group identity. -/
theorem idTangentSpace_zero_eq_one [IsFibered.InGroupoids p.op] (x : F) :
    (0 : idTangentSpace p x) = 1 := sorry

/-- Negation on the identity-tangent space is inversion in `Aut`. -/
instance instNeg_idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    Neg (idTangentSpace p x) where
  neg α := α⁻¹

/-- Additive inverse in `idTangentSpace` is the group inverse. -/
theorem idTangentSpace_neg_eq_inv [IsFibered.InGroupoids p.op] (x : F)
    (α : idTangentSpace p x) :
    -α = α⁻¹ := sorry

/-- Addition on `idTangentSpace`. -/
instance instAdd_idTangentSpace [HasRimSchlessinger p] (x : F) :
    Add (idTangentSpace p x) where
  add := idTangentSpaceAdd p

/-- Scalar multiplication on `idTangentSpace`. -/
instance instSMul_idTangentSpace [IsFibered.InGroupoids p.op] (x : F) :
    SMul k (idTangentSpace p x) where
  smul := idTangentSpaceSMul p

/-- The additive group structure on `T_id Aut(x)`. -/
instance instAddCommGroup_idTangentSpace [HasRimSchlessinger p] (x : F) :
    AddCommGroup (idTangentSpace p x) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The natural `k`-vector space structure on `T_id Aut(x)`. -/
instance instModule_idTangentSpace [HasRimSchlessinger p] (x : F) :
    Module k (idTangentSpace p x) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Addition in the identity-tangent `k`-module agrees with composition in `Aut`. -/
theorem idTangentSpace_add_eq_mul [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) : α + β = α * β := sorry

/-- In particular, composition of identity-tangent automorphisms is commutative. -/
theorem idTangentSpace_mul_comm [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x) : α * β = β * α := sorry

end CategoryTheory.Functor
