module

public import Mathlib.Algebra.BigOperators.Fin
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap95.«95_18_2_1_Stack»
public import stacks_project.Chap95.Definition_95_18_2
public import stacks_project.Chap95.Lemma_95_18_1
public import stacks_project.Chap97.Proposition_97_13_2_Action

/-!
# The Spec comparison `[X/G] ⟶ H_d`

The functor sending a `T`-point of the universal free-algebra scheme to the
pullback of the universal finite free projection, lifted along stackification
to a 1-morphism of stacks in groupoids `[X/G] ⟶ H_d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits CartesianMonoidalCategory
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.GLFixOne
open Functor.IsFibered.InGroupoids.Stackification
open Finset
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/-- The identity 1-morphism of the identity fibration on `(Sch/specZ)_fppf`. -/
abbrev identityBase : schemeBase specZ ⟶ schemeBase specZ :=
  𝟙 (schemeBase specZ)

/-- The finite Hilbert stack `H_d` of a point, over `specZ`. -/
abbrev hilbert (d : ℕ) [NeZero d] :
    StackOver.Groupoids (Scheme.fppfTopology.over specZ) :=
  ofScheme specZ d

/-- `hilbert d` is `ofScheme specZ d`. -/
theorem hilbert_eq (d : ℕ) [NeZero d] : hilbert d = ofScheme specZ d :=
  sorry

/-- The pullback of the universal family along a classifying map `T ⟶ baseScheme d`. -/
def specLeft {d : ℕ} [NeZero d] {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    Scheme.{u} :=
  pullback (projection d) f

/-- The finite locally free scheme over `U` classified by a map to `baseScheme d`. -/
def specOver {d : ℕ} [NeZero d] {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    Over specZ :=
  Over.mk (pullback.snd (projection d) f ≫ U.hom)

/-- The structure morphism of `specOver f` is the pullback of the universal projection. -/
def specπ {d : ℕ} [NeZero d] {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    specOver f ⟶ U :=
  Over.homMk (pullback.snd (projection d) f) sorry

/-- The underlying scheme morphism of `specπ f` is the second pullback projection. -/
theorem specπ_left {d : ℕ} [NeZero d] {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    (specπ f).left = pullback.snd (projection d) f :=
  sorry

/-- The pullback of the universal projection is finite locally free of rank `d`. -/
instance instIsFiniteLocallyFreeOfRank_specπ {d : ℕ} [NeZero d]
    {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    IsFiniteLocallyFreeOfRank (specπ f).left d :=
  sorry

/-- The object of `H_d` over `U` associated to a classifying map `T ⟶ baseScheme d`. -/
def specObj {d : ℕ} [NeZero d] {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    Obj identityBase d :=
  Obj.of U (specOver f) (specπ f) inferInstance
    (baseFiber U) (baseFiber (specOver f)) (ofSchemeIso (specπ f))

/-- The test scheme of `specObj f` is `U`. -/
theorem specObj_U {d : ℕ} [NeZero d] {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    (specObj f).U = U :=
  sorry

/-- The finite locally free scheme of `specObj f` is `specOver f`. -/
theorem specObj_Z {d : ℕ} [NeZero d] {U : Over specZ} (f : U.left ⟶ baseScheme d) :
    (specObj f).Z = specOver f :=
  sorry

/-- Morphisms `T ⟶ familyScheme d` correspond to ring maps out of the universal
algebra into global sections. -/
def familyHomCoeff (T : Scheme.{u}) (d : ℕ) [NeZero d] :
    (T ⟶ familyScheme d) ≃
      (UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤)) where
  toFun f :=
    (CommRingCat.Hom.hom
        (Scheme.homToSpecGlobalSectionsEquiv T
          (CommRingCat.of
            (ULift.{u}
              (UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩)))
          f)).comp
      ULift.ringEquiv.symm.toRingHom
  invFun ψ :=
    (Scheme.homToSpecGlobalSectionsEquiv T
        (CommRingCat.of
          (ULift.{u}
            (UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩)))).symm
      (CommRingCat.ofHom (ψ.comp ULift.ringEquiv.toRingHom))
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `familyHomCoeff` composes global sections with the universe-lift
equivalence. -/
theorem familyHomCoeff_apply (T : Scheme.{u}) (d : ℕ) [NeZero d] (f : T ⟶ familyScheme d) :
    familyHomCoeff T d f =
      (CommRingCat.Hom.hom
          (Scheme.homToSpecGlobalSectionsEquiv T
            (CommRingCat.of
              (ULift.{u}
                (UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩)))
            f)).comp
        ULift.ringEquiv.symm.toRingHom :=
  sorry

/-- The Yoneda morphism associated to a prestack point of `[X/_p G]`. -/
def classifyingPoint {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    AlgebraicSpace.ofOver ξ.base ⟶ (actionGroupoidSpace d).U.left :=
  yonedaEquiv.symm ξ.fiber

/-- `classifyingPoint` is the Yoneda equivalent of the functor-of-points fibre of `ξ`. -/
theorem classifyingPoint_eq {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    classifyingPoint ξ = yonedaEquiv.symm ξ.fiber :=
  sorry

/-- The free algebra classified by a prestack point of `[X/_p G]`. -/
def classifyingAlgebra {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    FreeDimAlgebra Γ(ξ.base.left, ⊤) d :=
  schemeHomEquiv ξ.base.left d (classifying (classifyingPoint ξ)).left

/-- `classifyingAlgebra` is `schemeHomEquiv` of the classifying scheme morphism. -/
theorem classifyingAlgebra_eq {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    classifyingAlgebra ξ =
      schemeHomEquiv ξ.base.left d (classifying (classifyingPoint ξ)).left :=
  sorry

/-- The classifying map of a prestack point of `[X/_p G]`. -/
def prestackClassifying {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    ξ.base.left ⟶ baseScheme d :=
  (schemeHomEquiv ξ.base.left d).symm (classifyingAlgebra ξ)

/-- `prestackClassifying` is the inverse `schemeHomEquiv` of `classifyingAlgebra`. -/
theorem prestackClassifying_eq {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    prestackClassifying ξ =
      (schemeHomEquiv ξ.base.left d).symm (classifyingAlgebra ξ) :=
  sorry

/-- The object of `H_d` associated to a prestack point of `[X/_p G]`. -/
def specPreObj {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    Obj identityBase d :=
  specObj (prestackClassifying ξ)

/-- `specPreObj ξ` is `specObj` of the classifying map of `ξ`. -/
theorem specPreObj_eq {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    specPreObj ξ = specObj (prestackClassifying ξ) :=
  sorry

/-- The relative spectrum of `O_U^{⊕ d}` with multiplication `m`. -/
def specAlgebra {d : ℕ} [NeZero d] {U : Over specZ}
    (m : FreeDimAlgebra Γ(U.left, ⊤) d) :
    Obj identityBase d :=
  specObj ((schemeHomEquiv U.left d).symm m)

/-- `specAlgebra m` is `specObj` of the classifying map of `m`. -/
theorem specAlgebra_eq {d : ℕ} [NeZero d] {U : Over specZ}
    (m : FreeDimAlgebra Γ(U.left, ⊤) d) :
    specAlgebra m = specObj ((schemeHomEquiv U.left d).symm m) :=
  sorry

/-- The functor-of-points arrow of a prestack morphism of `[X/_p G]`. -/
def prestackArrow {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    AlgebraicSpace.ofOver ξ.base ⟶ (actionGroupoidSpace d).R.left :=
  yonedaEquiv.symm p.fiber.arrow

/-- `prestackArrow p` is the Yoneda equivalent of the underlying arrow of `p.fiber`. -/
theorem prestackArrow_eq {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    prestackArrow p = yonedaEquiv.symm p.fiber.arrow :=
  sorry

/-- The unit-fixing matrix of a prestack morphism of `[X/_p G]`. -/
def prestackMatrix {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    glFixOne Γ(ξ.base.left, ⊤) d :=
  (homEquiv d ξ.base).toFun
    (classifyingGroup
      (prestackArrow p ≫ (fst (groupSpaceOp d).X (baseSpace d)).left))

/-- `prestackMatrix p` is `homEquiv` of the group component of `p.fiber`. -/
theorem prestackMatrix_eq {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    prestackMatrix p =
      (homEquiv d ξ.base).toFun
        (classifyingGroup
          (prestackArrow p ≫ (fst (groupSpaceOp d).X (baseSpace d)).left)) :=
  sorry

/-- Coefficient ring map of the conjugate of the algebra classified by `ψ`. -/
def conjugateCoeff {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (g : glFixOne Γ(T, ⊤) d)
    (ψ : UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤)) :
    UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤) :=
  schemeHomCoeff T d
    ((schemeHomEquiv T d).symm
      (FreeDimAlgebra.conjugate g
        (UniversalFiniteFreeAlgebra.schemeHomFreeDimAlgebra T ⟨d, Nat.pos_of_neZero d⟩
          (ψ.comp
            (CommRingCat.Hom.hom
              (UniversalFiniteFreeAlgebra.structureMap ⟨d, Nat.pos_of_neZero d⟩))))))

/-- `conjugateCoeff` is `schemeHomCoeff` of the conjugate classifying map. -/
theorem conjugateCoeff_eq {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (g : glFixOne Γ(T, ⊤) d)
    (ψ : UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤)) :
    conjugateCoeff g ψ =
      schemeHomCoeff T d
        ((schemeHomEquiv T d).symm
          (FreeDimAlgebra.conjugate g
            (UniversalFiniteFreeAlgebra.schemeHomFreeDimAlgebra T ⟨d, Nat.pos_of_neZero d⟩
              (ψ.comp
                (CommRingCat.Hom.hom
                  (UniversalFiniteFreeAlgebra.structureMap ⟨d, Nat.pos_of_neZero d⟩)))))) :=
  sorry

/-- Apply a unit-fixing matrix to a ring homomorphism out of the universal algebra, sending
basis coordinates `v` to `g • v` over the conjugate algebra. -/
def ringHomApplyLin {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (g : glFixOne Γ(T, ⊤) d)
    (ψ : UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤)) :
    UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤) where
  toFun x := ∑ i : Fin d, conjugateCoeff g ψ (x i) * g.val.val (fun j ↦ ψ (Pi.single j 1)) i
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `ringHomApplyLin g ψ` evaluates the conjugate coefficients on the transformed basis. -/
theorem ringHomApplyLin_apply {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (g : glFixOne Γ(T, ⊤) d)
    (ψ : UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤))
    (x : UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩) :
    ringHomApplyLin g ψ x =
      ∑ i : Fin d, conjugateCoeff g ψ (x i) * g.val.val (fun j ↦ ψ (Pi.single j 1)) i :=
  sorry

/-- Apply a unit-fixing matrix to a morphism into the universal family scheme. -/
def applyMatrixToFamily {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (g : glFixOne Γ(T, ⊤) d) (y : T ⟶ familyScheme d) :
    T ⟶ familyScheme d :=
  (familyHomCoeff T d).symm (ringHomApplyLin g (familyHomCoeff T d y))

/-- `applyMatrixToFamily` is `familyHomCoeff.symm` of `ringHomApplyLin`. -/
theorem applyMatrixToFamily_eq {T : Scheme.{u}} {d : ℕ} [NeZero d]
    (g : glFixOne Γ(T, ⊤) d) (y : T ⟶ familyScheme d) :
    applyMatrixToFamily g y =
      (familyHomCoeff T d).symm (ringHomApplyLin g (familyHomCoeff T d y)) :=
  sorry

/-- The family morphism `Spec(φ)` associated to a prestack arrow, using the unit-fixing
matrix of `p.fiber` on the tautological family point. -/
def specFamilyHom {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    specLeft (prestackClassifying ξ) ⟶ familyScheme d :=
  applyMatrixToFamily
    (GLFixOne.map
      (Scheme.Γ.map (pullback.snd (projection d) (prestackClassifying ξ)).op).hom
      (prestackMatrix p))
    (pullback.fst (projection d) (prestackClassifying ξ))

/-- `specFamilyHom p` applies the pulled-back matrix of `p` to the tautological family point. -/
theorem specFamilyHom_eq {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    specFamilyHom p =
      applyMatrixToFamily
        (GLFixOne.map
          (Scheme.Γ.map (pullback.snd (projection d) (prestackClassifying ξ)).op).hom
          (prestackMatrix p))
        (pullback.fst (projection d) (prestackClassifying ξ)) :=
  sorry

/-- `specFamilyHom p` lies over the conjugate classifying map of the source algebra. -/
theorem specFamilyHom_w {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    specFamilyHom p ≫ projection d =
      (pullback.snd (projection d) (prestackClassifying ξ) ≫ p.base.left) ≫
        prestackClassifying ξ' :=
  sorry

/-- The comparison of finite locally free schemes along a morphism of `[X/_p G]`, built from
the unit-fixing matrix of `p.fiber` and the test-scheme map `p.base`. -/
def specPreMapLeft {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total}
    (p : ξ ⟶ ξ') : (specPreObj ξ).Z.left ⟶ (specPreObj ξ').Z.left :=
  pullback.lift (specFamilyHom p)
    (pullback.snd (projection d) (prestackClassifying ξ) ≫ p.base.left)
    (specFamilyHom_w p)

/-- The underlying scheme morphism of `specPreMapLeft` is the lift of `specFamilyHom`
and the base change of `p.base`. -/
theorem specPreMapLeft_eq {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    specPreMapLeft p =
      pullback.lift (specFamilyHom p)
        (pullback.snd (projection d) (prestackClassifying ξ) ≫ p.base.left)
        (specFamilyHom_w p) :=
  sorry

/-- The morphism of `H_d` associated to a morphism of `[X/_p G]`. -/
def specPreMap {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    specPreObj ξ ⟶ specPreObj ξ' :=
  Hom.homMk p.base
    (Over.homMk (specPreMapLeft p) sorry) sorry sorry
    (baseRestrictIso p.base).symm
    (baseRestrictIso (Over.homMk (specPreMapLeft p) sorry)).symm
    sorry

/-- The underlying test-scheme map of `specPreMap p` is `p.base`. -/
theorem specPreMap_f {d : ℕ} [NeZero d]
    {ξ ξ' : ((actionGroupoidSpace d).preQuotient).total} (p : ξ ⟶ ξ') :
    (specPreMap p).f = p.base :=
  sorry

/-- The Spec functor `FA_d → H_d` on the action-groupoid prestack. -/
def specPreFunctor (d : ℕ) [NeZero d] :
    ((actionGroupoidSpace d).preQuotient).total ⥤ Obj identityBase d where
  obj ξ := specPreObj ξ
  map p := specPreMap p
  map_id := sorry
  map_comp := sorry

/-- `specPreFunctor` sends a prestack point to `specPreObj`. -/
theorem specPreFunctor_obj (d : ℕ) [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    (specPreFunctor d).obj ξ = specPreObj ξ :=
  sorry

/-- `specPreFunctor` lies over `(Sch/specZ)_fppf`. -/
theorem specPreFunctor_w (d : ℕ) [NeZero d] :
    specPreFunctor d ⋙ p identityBase d = ((actionGroupoidSpace d).preQuotient).p :=
  sorry

/-- The cartesian 1-morphism `Spec : [X/_p G] ⟶ H_d` over `(Sch/specZ)_fppf`. -/
def specPre (d : ℕ) [NeZero d] :
    CartesianBasedFunctor ((actionGroupoidSpace d).preQuotient).p (hilbert d).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (specPreFunctor d) (specPreFunctor_w d))

/-- The underlying functor of `specPre` is `specPreFunctor`. -/
theorem specPre_toFunctor (d : ℕ) [NeZero d] :
    (specPre d).toFunctor = specPreFunctor d :=
  sorry

/-- The selected stackification lift of `Spec` through `[X/_p G] ⟶ [X/G]`. -/
def homLift (d : ℕ) [NeZero d] :=
  CartesianBasedFunctor.IsStackification.liftChoice
    ((actionGroupoidSpace d).stackificationPresentation).isStackification (specPre d)

/-- The comparison 1-morphism `[X/G] ⟶ H_d` of stacks in groupoids over `(Sch/specZ)_fppf`. -/
def comparison (d : ℕ) [NeZero d] : quotient d ⟶ (hilbert d).toGroupoids :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor (homLift d).lift.toBasedFunctor

/-- Precomposing `comparison` with stackification of `[X/_p G]` recovers `specPre`. -/
def comparison_spec (d : ℕ) [NeZero d] :
    (CartesianBasedFunctor.precomp (hilbert d).p
        ((actionGroupoidSpace d).stackificationPresentation).comparison).obj
      (homLift d).lift ≅ specPre d :=
  (homLift d).comparison

/-- On a `T`-point of `X` classified by a free algebra `m`, `comparison` is the
relative spectrum of `O_T^{⊕ d}` with multiplication `m`. -/
theorem comparison_hom_app {d : ℕ} [NeZero d]
    (ξ : ((actionGroupoidSpace d).preQuotient).total) :
    (specPreFunctor d).obj ξ = specAlgebra (classifyingAlgebra ξ) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
