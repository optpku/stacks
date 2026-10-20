module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# The vanishing functor of a module morphism on an algebraic space

This module defines the subterminal functor on schemes over an algebraic space `B` that records
the base changes on which a morphism of quasi-coherent modules vanishes, and the corresponding
subfunctor of `B.functorOfPoints` on schemes over `S`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- Vanishing of a base-changed module morphism is preserved by restriction of the test
scheme over `B`. -/
theorem baseChangeMap_eq_zero {T T' : SchemeOver B} (φ : T' ⟶ T) (u : ℱ ⟶ 𝒢)
    (h : baseChangeMap f T.hom u = 0) :
    baseChangeMap f T'.hom u = 0 :=
  sorry

/-- Vanishing of `u_T` is preserved by further base change along a morphism of schemes
over `S`. -/
theorem baseChangeMap_eq_zero_of_over {T T' : Over S} (a : ofOver T ⟶ B) (φ : T' ⟶ T)
    (u : ℱ ⟶ 𝒢) (h : baseChangeMap f a u = 0) :
    baseChangeMap f (ofOverMap φ ≫ a) u = 0 :=
  sorry

/-- The subfunctor of the terminal `PUnit` functor cut out by vanishing of the
base-changed module morphism. -/
def zeroSubfunctor (u : ℱ ⟶ 𝒢) :
    CategoryTheory.Subfunctor
      ((Functor.const (SchemeOver B)ᵒᵖ).obj (PUnit : Type u)) where
  obj T := fun _ ↦ baseChangeMap f T.unop.hom u = 0
  map a _ h := baseChangeMap_eq_zero f a.unop u h

/-- Membership of the terminal section is exactly vanishing of the base-changed module
morphism. -/
theorem mem_zeroSubfunctor (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    PUnit.unit ∈ (zeroSubfunctor f u).obj (op T) ↔
      baseChangeMap f T.hom u = 0 :=
  sorry

/-- The contravariant subterminal functor recording where a module morphism vanishes
after base change to a scheme over `B`. -/
def zeroFunctor (u : ℱ ⟶ 𝒢) : (SchemeOver B)ᵒᵖ ⥤ Type u :=
  (zeroSubfunctor f u).toFunctor

/-- `zeroFunctor f u` is the underlying functor of `zeroSubfunctor f u`. -/
theorem zeroFunctor_def (u : ℱ ⟶ 𝒢) :
    zeroFunctor f u = (zeroSubfunctor f u).toFunctor :=
  sorry

/-- Every object value of the vanishing functor has at most one element. -/
instance zeroFunctorObjSubsingleton (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    Subsingleton ((zeroFunctor f u).obj (op T)) :=
  sorry

/-- An object value of the vanishing functor is inhabited exactly when the base-changed
morphism is zero. -/
theorem zeroFunctor_obj_nonempty_iff (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    Nonempty ((zeroFunctor f u).obj (op T)) ↔
      baseChangeMap f T.hom u = 0 :=
  sorry

/-- An object value of the vanishing functor is empty exactly when the base-changed
morphism is not zero. -/
theorem zeroFunctor_obj_isEmpty_iff (u : ℱ ⟶ 𝒢) (T : SchemeOver B) :
    IsEmpty ((zeroFunctor f u).obj (op T)) ↔
      ¬ baseChangeMap f T.hom u = 0 :=
  sorry

/-- A morphism `a : ofOver T ⟶ B` is a section of `zeroFunctor` iff the pullback of `u`
along `a` vanishes. -/
theorem zeroFunctor_obj_nonempty_iff_mk {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢) :
    Nonempty ((zeroFunctor f u).obj (op (SchemeOver.mk a))) ↔
      baseChangeMap f a u = 0 :=
  sorry

/-- The vanishing functor of Situation 77.7.1, as a subfunctor of the functor of points of
`B` on schemes over `S`: a morphism `ofOver T ⟶ B` lies in `F_zero` precisely when the
pullback of `u` along it vanishes. -/
def zeroOverSSubfunctor (u : ℱ ⟶ 𝒢) : Subfunctor B.functorOfPoints where
  obj T := {φ | baseChangeMap f (yonedaEquiv.symm φ) u = 0}
  map := sorry

/-- Membership in the `(Sch/S)` vanishing subfunctor is vanishing of the pullback of `u`
along the corresponding morphism `ofOver T ⟶ B`. -/
theorem mem_zeroOverSSubfunctor (u : ℱ ⟶ 𝒢) {T : Over S}
    (φ : B.functorOfPoints.obj (op T)) :
    φ ∈ (zeroOverSSubfunctor f u).obj (op T) ↔
      baseChangeMap f (yonedaEquiv.symm φ) u = 0 :=
  sorry

/-- The vanishing functor of Situation 77.7.1, as a functor `(Over S)ᵒᵖ ⥤ Type u`. -/
def zeroOverSFunctor (u : ℱ ⟶ 𝒢) : (Over S)ᵒᵖ ⥤ Type u :=
  (zeroOverSSubfunctor f u).toFunctor

/-- `zeroOverSFunctor f u` is the underlying functor of `zeroOverSSubfunctor f u`. -/
theorem zeroOverSFunctor_def (u : ℱ ⟶ 𝒢) :
    zeroOverSFunctor f u = (zeroOverSSubfunctor f u).toFunctor :=
  sorry

/-- The structural morphism `F_zero ⟶ B` of functors of points. -/
def zeroOverSFunctor_toB (u : ℱ ⟶ 𝒢) :
    zeroOverSFunctor f u ⟶ B.functorOfPoints :=
  (zeroOverSSubfunctor f u).ι

/-- `zeroOverSFunctor_toB f u` is the subfunctor inclusion of `zeroOverSSubfunctor f u`. -/
theorem zeroOverSFunctor_toB_eq (u : ℱ ⟶ 𝒢) :
    zeroOverSFunctor_toB f u = (zeroOverSSubfunctor f u).ι :=
  sorry

/-- A scheme `T` over `S` has an `F_zero`-point if and only if some morphism `ofOver T ⟶ B`
kills `u` after base change. -/
theorem zeroOverSFunctor_nonempty_iff (u : ℱ ⟶ 𝒢) (T : Over S) :
    Nonempty ((zeroOverSFunctor f u).obj (op T)) ↔
      ∃ a : ofOver T ⟶ B, baseChangeMap f a u = 0 :=
  sorry

namespace zeroOverSFunctor

/-- The algebraic space representing the `(Sch/S)` vanishing functor, when that functor is
an algebraic space. -/
def space (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (zeroOverSFunctor f u)] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (zeroOverSFunctor f u)

/-- The functor of points of `space f u` is `zeroOverSFunctor f u`. -/
theorem space_functorOfPoints (u : ℱ ⟶ 𝒢)
    [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    (space f u).functorOfPoints = zeroOverSFunctor f u :=
  sorry

/-- The structural morphism from the vanishing space to `B`. -/
def toB (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (zeroOverSFunctor f u)] : space f u ⟶ B :=
  zeroOverSFunctor_toB f u

/-- `toB f u` is the functor-of-points morphism `zeroOverSFunctor_toB f u`. -/
theorem toB_eq (u : ℱ ⟶ 𝒢) [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    toB f u = zeroOverSFunctor_toB f u :=
  sorry

end zeroOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
