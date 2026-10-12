/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap99.Situation_99_5_1

/-!
# Derived Euler data of a coherent family

An object `(T → B, F)` of `CohStack f` and a derived module `E` on `X` determine the
derived pullback `E_T` on the fibre `X_T`, the pushforward
`K = Rf_{T,*}(E_T ⊗ᴸ F[0])` on `T`, and the Euler characteristic function
`χ_K` on `Points T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Module sheaves on an algebraic space are monoidal. -/
instance instMonoidalCategory_modules {Y : AlgebraicSpace S} :
    MonoidalCategory Y.Modules :=
  modulesMonoidalCategory Y

/-- The tensor product of `𝒪`-modules is additive in each variable. -/
instance instMonoidalPreadditive_modules {Y : AlgebraicSpace S} :
    MonoidalPreadditive Y.Modules :=
  modulesMonoidalPreadditive Y

/-- Fixed-right derived tensor products exist for modules on an algebraic space. -/
instance instHasDerivedTensorRight {Y : AlgebraicSpace S} :
    DerivedTensor.Right.Has (C := Y.Modules) :=
  hasDerivedTensorRight Y

/-- The projection `X_T ⟶ X` of the fibre product along a test scheme over `B`. -/
def fiberToTotal (f : X ⟶ B) (σ : SchemesOver B) : fiber f σ ⟶ X :=
  pullback.fst f σ.hom

/-- The map `fiberToTotal f σ` is `pullback.fst f σ.hom`. -/
theorem fiberToTotal_eq (f : X ⟶ B) (σ : SchemesOver B) :
    fiberToTotal f σ = pullback.fst f σ.hom :=
  sorry

/-- The derived pullback `E_T = L(X_T ⟶ X)^* E` of a derived `𝒪_X`-module to the
fibre of an object of `CohStack f`. -/
def Obj.derivedPullback {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) : ModuleDerived (fiber f x.σ) :=
  (ModuleDerived.pullback (fiberToTotal f x.σ)).obj E

/-- `derivedPullback` is derived pullback along `fiberToTotal`. -/
theorem Obj.derivedPullback_eq {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) :
    x.derivedPullback E = (ModuleDerived.pullback (fiberToTotal f x.σ)).obj E :=
  sorry

/-- Derived tensor of a derived module with an `𝒪`-module placed in degree 0. -/
def tensorSingle {Y : AlgebraicSpace S} (K : ModuleDerived Y) (F : Y.Modules) :
    ModuleDerived Y :=
  Right.obj K ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj F)

/-- `tensorSingle` is derived tensor with the degree-zero single complex. -/
theorem tensorSingle_eq {Y : AlgebraicSpace S} (K : ModuleDerived Y) (F : Y.Modules) :
    tensorSingle K F =
      Right.obj K ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj F) :=
  sorry

/-- The object `K = Rf_{T,*}(E_T ⊗ᴸ F[0])` of `D(𝒪_T)` associated to an object of
`CohStack f` and a derived `𝒪_X`-module `E`. -/
def Obj.numericalPushforward {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) : ModuleDerived (ofOver x.σ.left) :=
  (pushforwardDerived (fiberToBase f x.σ)).obj
    (tensorSingle (x.derivedPullback E) x.module)

/-- `numericalPushforward` is derived pushforward of `E_T ⊗ᴸ F[0]` along
`fiberToBase`. -/
theorem Obj.numericalPushforward_eq {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (E : ModuleDerived X) :
    x.numericalPushforward E =
      (pushforwardDerived (fiberToBase f x.σ)).obj
        (tensorSingle (x.derivedPullback E) x.module) :=
  sorry

/-- The Euler characteristic `χ_E` of `numericalPushforward x E`, as a function on
the algebraic-space points of the test scheme `T`. -/
def Obj.eulerChar {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) : Points (ofOver x.σ.left) → ℤ :=
  ModuleDerived.fiberEulerChar (x.numericalPushforward E)

/-- The value of `eulerChar` at a point is the derived-fiber Euler characteristic of
`numericalPushforward`. -/
theorem Obj.eulerChar_apply {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) (t : Points (ofOver x.σ.left)) :
    x.eulerChar E t = ModuleDerived.fiberEulerChar (x.numericalPushforward E) t :=
  sorry

/-- The Euler characteristic as a function on the underlying scheme `|T|`, via
`ofOver.pointsEquiv`. -/
def Obj.eulerChar_scheme {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) : x.σ.left.left → ℤ :=
  fun t ↦ x.eulerChar E (ofOver.pointsEquiv x.σ.left t)

/-- `eulerChar_scheme` is `eulerChar` transported along `ofOver.pointsEquiv`. -/
theorem Obj.eulerChar_scheme_apply {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) (t : x.σ.left.left) :
    x.eulerChar_scheme E t = x.eulerChar E (ofOver.pointsEquiv x.σ.left t) :=
  sorry

/-- If `E` is perfect, then `K = Rf_{T,*}(E_T ⊗ᴸ F[0])` is perfect. -/
theorem Obj.numericalPushforward_isPerfect {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) {E : ModuleDerived X} (hE : ModuleDerived.IsPerfect E) :
    ModuleDerived.IsPerfect (x.numericalPushforward E) :=
  sorry

/-- The derived fibre `E_t ⊗ᴸ F_t` on `X_t = X_T ×_T Spec(κ(t))`. -/
def Obj.fibreTensor {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) (t : FieldValuedPoint (ofOver x.σ.left)) :
    ModuleDerived (pullback (fiberToBase f x.σ) t.hom) :=
  tensorSingle
    ((ModuleDerived.pullback (pullback.fst (fiberToBase f x.σ) t.hom)).obj
      (x.derivedPullback E))
    ((Modules.pullback (pullback.fst (fiberToBase f x.σ) t.hom)).obj x.module)

/-- `fibreTensor` is derived tensor of the pullbacks of `E_T` and `F` to `X_t`. -/
theorem Obj.fibreTensor_eq {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) (t : FieldValuedPoint (ofOver x.σ.left)) :
    x.fibreTensor E t =
      tensorSingle
        ((ModuleDerived.pullback (pullback.fst (fiberToBase f x.σ) t.hom)).obj
          (x.derivedPullback E))
        ((Modules.pullback (pullback.fst (fiberToBase f x.σ) t.hom)).obj x.module) :=
  sorry

/-- Derived pushforward of `E_t ⊗ᴸ F_t` to `Spec(κ(t))`. -/
def Obj.fibreTensorPushforward {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (E : ModuleDerived X) (t : FieldValuedPoint (ofOver x.σ.left)) :
    ModuleDerived (ofOver t.overObj) :=
  (pushforwardDerived (pullback.snd (fiberToBase f x.σ) t.hom)).obj (x.fibreTensor E t)

/-- `fibreTensorPushforward` is `R(X_t ⟶ Spec(κ(t)))_*(E_t ⊗ᴸ F_t)`. -/
theorem Obj.fibreTensorPushforward_eq {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (E : ModuleDerived X) (t : FieldValuedPoint (ofOver x.σ.left)) :
    x.fibreTensorPushforward E t =
      (pushforwardDerived (pullback.snd (fiberToBase f x.σ) t.hom)).obj
        (x.fibreTensor E t) :=
  sorry

/-- Formation of `numericalPushforward` commutes with restriction along a morphism
of `CohStack` objects: `L(T ⟶ T')^* K_{T'} ≅ K_T`. -/
theorem Hom.numericalPushforward_iso {f : X ⟶ B} [FinitePresentation f]
    {x y : Obj f} (α : Hom x y) (E : ModuleDerived X)
    (hE : ModuleDerived.IsPerfect E) :
    Nonempty
      ((ModuleDerived.pullback (ofOverMap α.base.left)).obj (y.numericalPushforward E) ≅
        x.numericalPushforward E) :=
  sorry

/-- Euler characteristics are compatible with restriction along a morphism of
`CohStack` objects. -/
theorem Hom.eulerChar_comp {f : X ⟶ B} [FinitePresentation f] {x y : Obj f}
    (α : Hom x y) (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) :
    x.eulerChar E = y.eulerChar E ∘ Points.map (ofOverMap α.base.left) :=
  sorry

/-- The function `χ` of `K` at `t` agrees with the Euler characteristic of the
derived fibre `E_t ⊗ᴸ F_t` on `X_t`. -/
theorem Obj.eulerChar_eq_fibreTensor {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E)
    (t : FieldValuedPoint (ofOver x.σ.left)) :
    x.eulerChar E (Points.mk t) =
      ModuleDerived.fiberEulerChar (x.fibreTensorPushforward E t)
        (Points.mk (FieldValuedPoint.of t.K t.structureHom (𝟙 (ofOver t.overObj)))) :=
  sorry

/-- If `E` is perfect, then `eulerChar x E` is locally constant on `Points T`. -/
theorem Obj.eulerChar_isLocallyConstant {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) {E : ModuleDerived X} (hE : ModuleDerived.IsPerfect E) :
    IsLocallyConstant (x.eulerChar E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
