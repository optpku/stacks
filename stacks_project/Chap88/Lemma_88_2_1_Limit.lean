module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.Algebra.Category.CommAlgCat.Module
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import ReasLib.RingTheory.AdicCompletion.InverseSystem
public import stacks_project.Chap88.«88_2_0_3»

/-!
# Inverse limits of finite-type adic algebra systems

The inverse-limit functor `C ⥤ C'` sending a finite-type adic inverse system
`(B n)` to `lim B n`, together with explicit unit and counit comparison maps
against `toAdicSystem`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PNatInverseSystem
noncomputable section

universe u

namespace AdicAlgebraSystem

variable {A : Type u} [CommRing A]

/-- The `A`-algebra structure on an arbitrary stage of an inverse system over
`quotientSystem I`, obtained from `instAlgebra` at `OrderDual.ofDual i`. -/
instance instAlgebraObj (I : Ideal A) (B : Under (quotientSystem I))
    (i : OrderDual ℕ+) :
    Algebra A (B.right.obj i) :=
  instAlgebra I B (OrderDual.ofDual i)

/-- The transition `B i ⟶ B j` of an inverse system over `quotientSystem I`,
as an `A`-algebra map. -/
def transitionAlgHom (I : Ideal A) (B : Under (quotientSystem I))
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    B.right.obj i →ₐ[A] B.right.obj j where
  toRingHom := (B.right.map f).hom
  commutes' := sorry

/-- Unfolding of `transitionAlgHom` as the underlying ring homomorphism of the
inverse-system transition. -/
theorem transitionAlgHom_toRingHom (I : Ideal A) (B : Under (quotientSystem I))
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (transitionAlgHom I B f).toRingHom = (B.right.map f).hom :=
  sorry

/-- The diagram `n ↦ B n` of an object of `C`, valued in commutative
`A`-algebras. -/
def stageDiagram (I : Ideal A) (B : AdicAlgebraSystem A I) :
    PNatInverseSystem (CommAlgCat.{u} A) where
  obj i := CommAlgCat.of A (B.obj.right.obj i)
  map f := CommAlgCat.ofHom (transitionAlgHom I B.obj f)
  map_id := sorry
  map_comp := sorry

/-- Stages of `stageDiagram I B` are the stages of `B` as `A`-algebras. -/
theorem stageDiagram_obj (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (stageDiagram I B).obj i = CommAlgCat.of A (B.obj.right.obj i) :=
  sorry

/-- A morphism of objects of `C` induces a morphism of `A`-algebra diagrams. -/
def stageDiagramMap (I : Ideal A) {B B' : AdicAlgebraSystem A I} (f : B ⟶ B') :
    stageDiagram I B ⟶ stageDiagram I B' where
  app i :=
    CommAlgCat.ofHom
      { toRingHom := (Under.Hom.right f.hom).app i |>.hom
        commutes' := sorry }
  naturality := sorry

/-- The underlying `A`-module diagram of an object of `C`. -/
def stageModuleDiagram (I : Ideal A) (B : AdicAlgebraSystem A I) :
    PNatInverseSystem (ModuleCat.{u} A) :=
  stageDiagram I B ⋙ CommAlgCat.forgetToModule A

/-- Stages of `stageModuleDiagram` are the stages of `B` as `A`-modules. -/
theorem stageModuleDiagram_obj (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (stageModuleDiagram I B).obj i =
      (CommAlgCat.forgetToModule A).obj ((stageDiagram I B).obj i) :=
  sorry

/-- The underlying commutative-ring diagram of an object of `C`. -/
def stageRingDiagram (I : Ideal A) (B : AdicAlgebraSystem A I) :
    PNatInverseSystem CommRingCat.{u} :=
  stageDiagram I B ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u}

/-- Stages of `stageRingDiagram` are the underlying rings of the stages of
`B`. -/
theorem stageRingDiagram_obj (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (stageRingDiagram I B).obj i =
      (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj
        ((stageDiagram I B).obj i) :=
  sorry


/-- The inverse limit `lim B n` of an object of `C`, as a commutative
`A`-algebra. -/
def limitObj (I : Ideal A) (B : AdicAlgebraSystem A I) : CommAlgCat.{u} A :=
  limit (stageDiagram I B)

/-- `limitObj` is the categorical limit of `stageDiagram`. -/
theorem limitObj_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    limitObj I B = limit (stageDiagram I B) :=
  sorry

/-- For finitely generated `I`, the inverse limit of an object of `C` is
topologically of finite type. -/
theorem limitObj_topologicallyFiniteType (I : Ideal A) (hI : I.FG)
    (B : AdicAlgebraSystem A I) :
    Algebra.TopologicallyFiniteType I (limitObj I B) :=
  sorry

/-- The inverse-limit functor `C ⥤ C'` sending `(B n)` to `lim B n`. -/
def limitFunctor (I : Ideal A) (hI : I.FG) :
    AdicAlgebraSystem A I ⥤ CommAlgCat.TopologicallyFiniteType.{u} A I where
  obj B := ⟨limitObj I B, limitObj_topologicallyFiniteType I hI B⟩
  map f := ObjectProperty.homMk (limMap (stageDiagramMap I f))
  map_id := sorry
  map_comp := sorry

/-- On objects, `limitFunctor` is `limitObj`. -/
theorem limitFunctor_obj (I : Ideal A) (hI : I.FG) (B : AdicAlgebraSystem A I) :
    ((limitFunctor I hI).obj B).obj = limitObj I B :=
  sorry

/-- On morphisms, `limitFunctor` is induced by `limMap` of `stageDiagramMap`. -/
theorem limitFunctor_map (I : Ideal A) (hI : I.FG)
    {B B' : AdicAlgebraSystem A I} (f : B ⟶ B') :
    ((limitFunctor I hI).map f).hom = limMap (stageDiagramMap I f) :=
  sorry

/-- The canonical `A`-algebra map from a complete algebra to a finite adic
quotient stage of its quotient system. -/
def completeQuotientAlgHom (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    (n : ℕ+) :
    B →ₐ[A] (CommAlgCat.adicQuotientUnder I B).right.stage n where
  toRingHom := Ideal.Quotient.mk ((I ^ (n : ℕ)).map (algebraMap A B))
  commutes' := sorry

/-- The cone of quotient maps `B ⟶ B ⧸ I ^ n B` on the image under
`toAdicSystem`. -/
def completeQuotientCone (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    Cone (stageDiagram I
      ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) where
  pt := B.obj
  π :=
    { app := fun i ↦
        CommAlgCat.ofHom (completeQuotientAlgHom I B.obj (OrderDual.ofDual i))
      naturality := sorry }

/-- The canonical comparison `B ⟶ lim (B ⧸ I ^ n B)` from the quotient cone. -/
def toLimitObjAlgHom (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    B.obj →ₐ[A]
      limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) :=
  (limit.lift
      (stageDiagram I
        ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B))
      (completeQuotientCone I B)).hom

/-- Completeness along `I` implies completeness along the extended ideal
`I B`. -/
instance instIsAdicComplete_map (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] [IsAdicComplete I B] :
    IsAdicComplete (I.map (algebraMap A B)) B :=
  sorry

/-- Projection of `lim (B ⧸ I ^ n B)` onto a positive adic quotient of `B`. -/
def limitObj_π_quotient (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) (n : ℕ+) :
    limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) →ₐ[A]
      B.obj ⧸ (I ^ (n : ℕ)).map (algebraMap A B.obj) where
  toFun :=
    (limit.π
        (stageDiagram I
          ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B))
        (OrderDual.toDual n)).hom
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Evaluation of the inverse limit of `(B ⧸ I ^ n B)` at a nonnegative stage,
as a map into `B ⧸ (I B) ^ n`. -/
def limitObjEvalFamily (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) (n : ℕ) :
    limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) →ₐ[A]
      B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n :=
  if hn : 0 < n then
    (Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A B.obj) I n)).toAlgHom.comp
      (limitObj_π_quotient I B ⟨n, hn⟩)
  else
    { toFun := fun _ ↦ 0
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }

/-- Compatibility of `limitObjEvalFamily` with the adic quotient tower. -/
theorem limitObjEvalFamily_comp (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
        (limitObjEvalFamily I B n) =
      limitObjEvalFamily I B m :=
  sorry

/-- The inverse comparison `lim (B ⧸ I ^ n B) ⟶ B` for an object of `C'`, via
`AdicCompletion.liftAlgHom` and `AdicCompletion.ofAlgEquiv`. -/
def fromLimitObjAlgHom (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) →ₐ[A]
      B.obj :=
  ((AdicCompletion.ofAlgEquiv (I.map (algebraMap A B.obj))).symm.toAlgHom.restrictScalars
        A).comp
    (AdicCompletion.liftAlgHom (I.map (algebraMap A B.obj))
      (limitObjEvalFamily I B) (limitObjEvalFamily_comp I B))

/-- The canonical algebra equivalence `B ≃ₐ[A] lim (B ⧸ I ^ n B)` for an object
of `C'`. -/
def completeLimitAlgEquiv (I : Ideal A) (hI : I.FG)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    B.obj ≃ₐ[A]
      ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I ⋙
          limitFunctor I hI).obj B).obj :=
  AlgEquiv.ofAlgHom (toLimitObjAlgHom I B) (fromLimitObjAlgHom I B) sorry sorry

/-- The constant ring cone on `stageRingDiagram` with vertex `A`. -/
def algebraMapRingCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageRingDiagram I B) where
  pt := CommRingCat.of A
  π.app i :=
    CommRingCat.ofHom (algebraMap A ((stageDiagram I B).obj i))
  π.naturality := sorry

/-- The vertex of `algebraMapRingCone` is `A`. -/
theorem algebraMapRingCone_pt (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (algebraMapRingCone I B).pt = CommRingCat.of A :=
  sorry

/-- The inverse limit of the underlying ring diagram carries its canonical
`A`-algebra structure, with structure map the limit of the stage structure
maps. -/
instance instAlgebra_limit_stageRingDiagram (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    Algebra A (limit (stageRingDiagram I B) : CommRingCat.{u}) where
  smul r x :=
    (limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom r * x
  algebraMap :=
    (limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom
  commutes' := sorry
  smul_def' := sorry

/-- The structure map of the ring-limit algebra is the lift of
`algebraMapRingCone`. -/
theorem algebraMap_limit_stageRingDiagram (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    algebraMap A (limit (stageRingDiagram I B) : CommRingCat.{u}) =
      (limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom :=
  sorry

/-- The forgotten limit cone of `stageDiagram`, as a cone on
`stageRingDiagram`. -/
def limitObjRingCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageRingDiagram I B) where
  pt := (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj (limitObj I B)
  π.app i :=
    (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map
      (limit.π (stageDiagram I B) i)
  π.naturality := sorry

/-- The canonical ring comparison from the algebra limit to the ring limit. -/
def toRingLimitHom (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj (limitObj I B) ⟶
      limit (stageRingDiagram I B) :=
  limit.lift (stageRingDiagram I B) (limitObjRingCone I B)

/-- `toRingLimitHom` is the lift of `limitObjRingCone`. -/
theorem toRingLimitHom_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    toRingLimitHom I B =
      limit.lift (stageRingDiagram I B) (limitObjRingCone I B) :=
  sorry

/-- Projection from the ring limit to a stage, as an `A`-algebra map. -/
def ringLimitπAlgHom (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (limit (stageRingDiagram I B) : CommRingCat.{u}) →ₐ[A]
      (stageDiagram I B).obj i where
  toFun := (limit.π (stageRingDiagram I B) i).hom
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Unfolding of `ringLimitπAlgHom` as the underlying ring-limit
projection. -/
theorem ringLimitπAlgHom_toFun (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) (x : (limit (stageRingDiagram I B) : CommRingCat.{u})) :
    ringLimitπAlgHom I B i x = (limit.π (stageRingDiagram I B) i).hom x :=
  sorry

/-- The ring limit, viewed as an `A`-algebra, as a cone on `stageDiagram`. -/
def ringLimitAlgebraCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageDiagram I B) where
  pt := CommAlgCat.of A (limit (stageRingDiagram I B) : CommRingCat.{u})
  π.app i := CommAlgCat.ofHom (ringLimitπAlgHom I B i)
  π.naturality := sorry

/-- The canonical `A`-algebra comparison from the ring limit to the algebra
limit. -/
def fromRingLimitAlgHom (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limit (stageRingDiagram I B) : CommRingCat.{u}) →ₐ[A] limitObj I B :=
  (limit.lift (stageDiagram I B) (ringLimitAlgebraCone I B)).hom

/-- `fromRingLimitAlgHom` is the lift of `ringLimitAlgebraCone`. -/
theorem fromRingLimitAlgHom_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    fromRingLimitAlgHom I B =
      (limit.lift (stageDiagram I B) (ringLimitAlgebraCone I B)).hom :=
  sorry

/-- The forgotten limit cone of `stageDiagram`, as a cone on
`stageModuleDiagram`. -/
def limitObjModuleCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageModuleDiagram I B) where
  pt := ModuleCat.of A (limitObj I B)
  π.app i :=
    (CommAlgCat.forgetToModule A).map (limit.π (stageDiagram I B) i)
  π.naturality := sorry

/-- The canonical `A`-linear comparison from the algebra limit to the module
limit. -/
def toModuleLimitLinearMap (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limitObj I B : Type u) →ₗ[A]
      (limit (stageModuleDiagram I B) : ModuleCat A) :=
  (limit.lift (stageModuleDiagram I B) (limitObjModuleCone I B)).hom

/-- `toModuleLimitLinearMap` is the lift of `limitObjModuleCone`. -/
theorem toModuleLimitLinearMap_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    toModuleLimitLinearMap I B =
      (limit.lift (stageModuleDiagram I B) (limitObjModuleCone I B)).hom :=
  sorry

/-- The Type-valued diagrams of `stageModuleDiagram` and `stageRingDiagram`
are canonically isomorphic. -/
def stageForgetNatIso (I : Ideal A) (B : AdicAlgebraSystem A I) :
    stageModuleDiagram I B ⋙ forget (ModuleCat.{u} A) ≅
      stageRingDiagram I B ⋙ forget CommRingCat.{u} :=
  NatIso.ofComponents
    (fun i ↦
      eqToIso <|
        Eq.trans
          (rfl :
            (stageModuleDiagram I B ⋙ forget (ModuleCat.{u} A)).obj i =
              ((stageDiagram I B).obj i : Type u))
          (Eq.symm
            (rfl :
              (stageRingDiagram I B ⋙ forget CommRingCat.{u}).obj i =
                ((stageDiagram I B).obj i : Type u))))
    (fun {X Y} (f : X ⟶ Y) ↦ sorry)

/-- Named Type-identification of the module limit with the ring limit. -/
def moduleLimitToRingLimitEquiv (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limit (stageModuleDiagram I B) : ModuleCat A) ≃
      (limit (stageRingDiagram I B) : CommRingCat.{u}) :=
  { toFun :=
      (preservesLimitIso (forget CommRingCat.{u}) (stageRingDiagram I B)).inv ∘
        (HasLimit.isoOfNatIso (stageForgetNatIso I B)).hom ∘
          (preservesLimitIso (forget (ModuleCat.{u} A))
              (stageModuleDiagram I B)).hom
    invFun :=
      (preservesLimitIso (forget (ModuleCat.{u} A))
            (stageModuleDiagram I B)).inv ∘
        (HasLimit.isoOfNatIso (stageForgetNatIso I B)).inv ∘
          (preservesLimitIso (forget CommRingCat.{u})
              (stageRingDiagram I B)).hom
    left_inv := sorry
    right_inv := sorry }

/-- The inverse comparison from the module limit to the algebra limit. -/
def fromModuleLimit (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limit (stageModuleDiagram I B) : ModuleCat A) → limitObj I B :=
  fun x ↦ fromRingLimitAlgHom I B (moduleLimitToRingLimitEquiv I B x)

/-- `fromModuleLimit` factors through `fromRingLimitAlgHom`. -/
theorem fromModuleLimit_eq (I : Ideal A) (B : AdicAlgebraSystem A I)
    (x : (limit (stageModuleDiagram I B) : ModuleCat A)) :
    fromModuleLimit I B x =
      fromRingLimitAlgHom I B (moduleLimitToRingLimitEquiv I B x) :=
  sorry

/-- Named identification of the inverse limit in `CommAlgCat` with the inverse
limit of the underlying `A`-module diagram. -/
def limitObjModuleLinearEquiv (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limitObj I B : Type u) ≃ₗ[A]
      (limit (stageModuleDiagram I B) : ModuleCat A) :=
  { toModuleLimitLinearMap I B with
    invFun := fromModuleLimit I B
    left_inv := sorry
    right_inv := sorry }

/-- The forward map of `limitObjModuleLinearEquiv` is
`toModuleLimitLinearMap`. -/
theorem limitObjModuleLinearEquiv_apply (I : Ideal A)
    (B : AdicAlgebraSystem A I) (x : limitObj I B) :
    limitObjModuleLinearEquiv I B x = toModuleLimitLinearMap I B x :=
  sorry

/-- Named identification of the extended power `(I ^ n).map (algebraMap A B)`
with the submodule `I ^ n • ⊤`, after restriction of scalars to `A`. -/
theorem map_pow_restrictScalars_eq_smul_top (I : Ideal A) (B : Type u)
    [CommRing B] [Algebra A B] (n : ℕ) :
    ((I ^ n).map (algebraMap A B)).restrictScalars A =
      I ^ n • (⊤ : Submodule A B) :=
  sorry

/-- Successor maps of `stageModuleDiagram` are surjective. -/
theorem stageModuleDiagram_stepSurjective (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    ∀ n : ℕ+, Function.Surjective ((stageModuleDiagram I B).stepLinearMap n) :=
  sorry

/-- The kernel of a successor map of `stageModuleDiagram` is `I ^ n • ⊤`. -/
theorem stageModuleDiagram_ker_stepLinearMap (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    ∀ n : ℕ+,
      LinearMap.ker ((stageModuleDiagram I B).stepLinearMap n) =
        I ^ (n : ℕ) •
          (⊤ : Submodule A ((stageModuleDiagram I B).stage (n + 1))) :=
  sorry

/-- The descended limit projection `(lim B m) ⧸ I ^ n (lim B m) ⟶ B n`. -/
def limitQuotientToStageAlgHom (I : Ideal A) (B : AdicAlgebraSystem A I)
    (n : ℕ+) :
    (limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B))) →ₐ[A]
      B.obj.right.stage n where
  toRingHom :=
    Ideal.Quotient.lift ((I ^ (n : ℕ)).map (algebraMap A (limitObj I B)))
      (limit.π (stageDiagram I B) (OrderDual.toDual n)).hom.toRingHom
      (fun _ _ ↦ sorry)
  commutes' := sorry

/-- Named identification of the algebra-limit quotient by the extended power
of `I` with the module-limit quotient by `I ^ n • ⊤`. -/
def limitObjQuotientToModuleQuotient (I : Ideal A)
    (B : AdicAlgebraSystem A I) (n : ℕ+) :
    (limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B))) ≃ₗ[A]
      ((limit (stageModuleDiagram I B) : ModuleCat A) ⧸
        I ^ (n : ℕ) •
          (⊤ : Submodule A
            (limit (stageModuleDiagram I B) : ModuleCat A))) :=
  ((Submodule.Quotient.restrictScalarsEquiv A
          ((I ^ (n : ℕ)).map (algebraMap A (limitObj I B)))).symm.trans
      (Submodule.quotEquivOfEq _ _
        (map_pow_restrictScalars_eq_smul_top I (limitObj I B) n))).trans
    (Submodule.Quotient.equiv
      (I ^ (n : ℕ) • (⊤ : Submodule A (limitObj I B)))
      (I ^ (n : ℕ) •
        (⊤ : Submodule A (limit (stageModuleDiagram I B) : ModuleCat A)))
      (limitObjModuleLinearEquiv I B) sorry)

/-- The inverse comparison `B n ⟶ (lim B m) ⧸ I ^ n (lim B m)`, obtained from
the inverse of `limitProjectionQuotientEquiv` after the named limit and ideal
identifications. -/
def stageToLimitQuotientAlgHom (I : Ideal A) (hI : I.FG)
    (B : AdicAlgebraSystem A I) (n : ℕ+) :
    B.obj.right.stage n →ₐ[A]
      limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B)) :=
  AlgHom.ofLinearMap
    ((limitObjQuotientToModuleQuotient I B n).symm.toLinearMap.comp
      ((stageModuleDiagram I B).limitProjectionQuotientEquiv I hI
          (stageModuleDiagram_stepSurjective I B)
          (stageModuleDiagram_ker_stepLinearMap I B) n).symm.toLinearMap)
    sorry sorry

/-- The canonical algebra equivalence
`(lim B m) ⧸ I ^ n (lim B m) ≃ₐ[A] B n`, for finitely generated `I`. -/
def limitObjQuotientAlgEquiv (I : Ideal A) (hI : I.FG)
    (B : AdicAlgebraSystem A I) (n : ℕ+) :
    (limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B))) ≃ₐ[A]
      B.obj.right.stage n :=
  AlgEquiv.ofAlgHom (limitQuotientToStageAlgHom I B n)
    (stageToLimitQuotientAlgHom I hI B n) sorry sorry

/-- The right-leg isomorphism of inverse systems underlying the counit
comparison. -/
def limitFunctorCounitRightIso (I : Ideal A) (hI : I.FG)
    (B : AdicAlgebraSystem A I) :
    ((limitFunctor I hI ⋙
          CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B).obj.right ≅
      B.obj.right :=
  NatIso.ofComponents
    (fun i ↦
      RingEquiv.toCommRingCatIso
        (limitObjQuotientAlgEquiv I hI B (OrderDual.ofDual i)).toRingEquiv)
    (fun {X Y} (f : X ⟶ Y) ↦ sorry)

/-- The unit isomorphism `𝟭 C' ≅ toAdicSystem ⋙ limitFunctor`. -/
def limitFunctorUnitIso (I : Ideal A) (hI : I.FG) :
    𝟭 (CommAlgCat.TopologicallyFiniteType.{u} A I) ≅
      CommAlgCat.TopologicallyFiniteType.toAdicSystem I ⋙ limitFunctor I hI :=
  NatIso.ofComponents
    (fun B ↦
      CommAlgCat.TopologicallyFiniteType.isoMk (completeLimitAlgEquiv I hI B))
    (fun {X Y} (f : X ⟶ Y) ↦ sorry)

/-- The counit isomorphism `limitFunctor ⋙ toAdicSystem ≅ 𝟭 C`. -/
def limitFunctorCounitIso (I : Ideal A) (hI : I.FG) :
    limitFunctor I hI ⋙ CommAlgCat.TopologicallyFiniteType.toAdicSystem I ≅
      𝟭 (AdicAlgebraSystem A I) :=
  NatIso.ofComponents
    (fun B ↦
      ObjectProperty.isoMk _
        (Under.isoMk (limitFunctorCounitRightIso I hI B) sorry))
    (fun {X Y} (f : X ⟶ Y) ↦ sorry)

/-- Explicit quasi-inverse data for `toAdicSystem`, with inverse the
inverse-limit functor. -/
def limitFunctorQuasiInverse (I : Ideal A) (hI : I.FG) :
    (CommAlgCat.TopologicallyFiniteType.toAdicSystem I).QuasiInverse where
  inverse := limitFunctor I hI
  unitIso := limitFunctorUnitIso I hI
  counitIso := limitFunctorCounitIso I hI

/-- The inverse stored by `limitFunctorQuasiInverse` is `limitFunctor`. -/
theorem limitFunctorQuasiInverse_inverse (I : Ideal A) (hI : I.FG) :
    (limitFunctorQuasiInverse I hI).inverse = limitFunctor I hI :=
  sorry

/-- `limitFunctor` is a quasi-inverse of `toAdicSystem`. -/
theorem limitFunctor_isQuasiInverse (I : Ideal A) (hI : I.FG) :
    (limitFunctor I hI).IsQuasiInverse
      (CommAlgCat.TopologicallyFiniteType.toAdicSystem I) :=
  sorry

/-- The equivalence `C ≌ C'` induced by the inverse-limit functor and
`toAdicSystem`. -/
def limitFunctorEquivalence (I : Ideal A) (hI : I.FG) :
    AdicAlgebraSystem A I ≌ CommAlgCat.TopologicallyFiniteType.{u} A I :=
  CategoryTheory.Equivalence.mk (limitFunctor I hI)
    (CommAlgCat.TopologicallyFiniteType.toAdicSystem I)
    (limitFunctorCounitIso I hI).symm (limitFunctorUnitIso I hI).symm

end AdicAlgebraSystem
