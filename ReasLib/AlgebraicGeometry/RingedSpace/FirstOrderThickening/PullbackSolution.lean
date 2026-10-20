module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening

/-!
# Pullback solutions of first-order thickening problems

Given a first-order thickening `t : S ⟶ S'`, a morphism `f : X ⟶ S`, an `𝒪_X`-module
`G`, and a map `c : (f^*).obj (RingedSpace.Hom.idealModule t) ⟶ G`, a pullback solution
is a first-order thickening `i : X ⟶ X'` together with a compatible morphism
`f' : X' ⟶ S'` and a kernel identification inducing `c`.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S)

/-- The comparison `(f^*).obj (RingedSpace.Hom.idealModule t) ⟶ RingedSpace.Hom.idealModule i`
induced by `(f')♯` along a commutative square of first-order thickenings. -/
def pullbackKerMapOf {X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
    (f' : X' ⟶ S') (w : i ≫ f' = f ≫ t) :
    (f^*).obj (RingedSpace.Hom.idealModule t) ⟶ RingedSpace.Hom.idealModule i :=
  ((RingedSpace.Hom.pullbackCompIso f t).symm ≪≫
      eqToIso (congrArg (fun h : X ⟶ S' ↦ RingedSpace.Hom.pullback h) w.symm) ≪≫
      RingedSpace.Hom.pullbackCompIso i f').hom.app
    (RingedSpace.Hom.kernelIdealSheaf t) ≫
    (i^*).map (Hom.idealMap (homMk f f' w.symm : of i ⟶ of t))

variable {G : X.Modules} (c : (f^*).obj (RingedSpace.Hom.idealModule t) ⟶ G)

/-- A pullback solution is a first-order thickening `i : X ⟶ X'` with a compatible map
`f' : X' ⟶ S'`, a kernel identification with `G`, and induced pullback kernel map `c`. -/
structure PullbackSolution where
  /-- The ambient ringed space of the solution thickening. -/
  X' : RingedSpace.{u}
  /-- The thickening of `X` into the ambient ringed space. -/
  i : X ⟶ X'
  /-- The morphism `i` is a first-order thickening. -/
  [isFirstOrder : IsFirstOrderThickening i]
  /-- The morphism from the ambient ringed space to `S'`. -/
  f' : X' ⟶ S'
  /-- The square with `t` and `f` commutes. -/
  w : i ≫ f' = f ≫ t
  /-- The kernel module of `i` is identified with `G`. -/
  kernelIso : RingedSpace.Hom.idealModule i ≅ G
  /-- The kernel identification carries the induced comparison to `c`. -/
  induces : pullbackKerMapOf t f i f' w ≫ kernelIso.hom = c

namespace PullbackSolution

/-- Construct a pullback solution from a first-order thickening, a compatible ambient map,
a kernel identification, and the induced-map equality. -/
def of {X' : RingedSpace.{u}} (i : X ⟶ X') [isFirstOrder : IsFirstOrderThickening i]
    (f' : X' ⟶ S') (w : i ≫ f' = f ≫ t)
    (kernelIso : RingedSpace.Hom.idealModule i ≅ G)
    (induces : pullbackKerMapOf t f i f' w ≫ kernelIso.hom = c) :
    PullbackSolution t f c where
  X' := X'
  i := i
  isFirstOrder := isFirstOrder
  f' := f'
  w := w
  kernelIso := kernelIso
  induces := induces

/-- The morphism of bundled thickenings defined by a pullback solution. -/
def toHom (sol : PullbackSolution t f c) :
    -- Local instance justification (proof-local temporary data): bundled `sol.isFirstOrder` is not globally searched, but `Thickening.of sol.i` requires `IsThickening sol.i`.
    letI := sol.isFirstOrder
    Thickening.of sol.i ⟶ Thickening.of t :=
  -- Local instance justification (proof-local temporary data): bundled `sol.isFirstOrder` is not globally searched, but `homMk` via `Thickening.of sol.i` requires `IsThickening sol.i`.
  letI := sol.isFirstOrder
  homMk f sol.f' sol.w.symm

/-- The comparison from the pulled-back base kernel module to the solution kernel module. -/
def kerMap (sol : PullbackSolution t f c) :
    (f^*).obj (RingedSpace.Hom.idealModule t) ⟶ RingedSpace.Hom.idealModule sol.i :=
  -- Local instance justification (proof-local temporary data): bundled `sol.isFirstOrder` is not globally searched, but `pullbackKerMapOf` requires `IsFirstOrderThickening sol.i`.
  letI := sol.isFirstOrder
  pullbackKerMapOf t f sol.i sol.f' sol.w

/-- A pullback solution has a commutative square and its kernel identification induces `c`. -/
theorem spec (sol : PullbackSolution t f c) :
    sol.i ≫ sol.f' = f ≫ t ∧ sol.kerMap ≫ sol.kernelIso.hom = c := sorry

/-- The kernel identification of a pullback solution induces the prescribed map `c`. -/
theorem induces_eq (sol : PullbackSolution t f c) :
    sol.kerMap ≫ sol.kernelIso.hom = c := sorry

/-- The square of ringed spaces determined by a pullback solution is commutative. -/
theorem toCommSq (sol : PullbackSolution t f c) : CommSq sol.i f sol.f' t := sorry

end PullbackSolution

end AlgebraicGeometry.RingedSpace.Thickening
