/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReasLib.Algebra.Category.CommRingCat.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec

/-!
# A nonrepresentable flattening functor

This module defines a flattening functor over a two-variable polynomial ring whose infinitesimal
fibers are singletons but whose fiber over the power-series completion is empty.
-/

@[expose] public section

open CategoryTheory CategoryTheory.CommRingCat Opposite
  AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Flattening.Counterexample

/-- The `k[x, y]`-module obtained from `k[x, x⁻¹, y] / (y)` by restriction of scalars. -/
def module (k : Type u) [Field k] : ModuleCat.{u} (MvPolynomial (Fin 2) k) :=
  let R := MvPolynomial (Fin 2) k
  let L := Localization.Away (MvPolynomial.X (0 : Fin 2) : R)
  let J : Ideal L :=
    Ideal.span ({algebraMap R L (MvPolynomial.X (1 : Fin 2))} : Set L)
  let algebraMapToQuotient : R →+* L ⧸ J :=
    (Ideal.Quotient.mk J).comp (algebraMap R L)
  (ModuleCat.restrictScalars algebraMapToQuotient).obj (ModuleCat.of (L ⧸ J) (L ⧸ J))

/-- The explicit localization-then-quotient presentation of `module k`. -/
theorem module_def (k : Type u) [Field k] :
    module k =
      let R := MvPolynomial (Fin 2) k
      let L := Localization.Away (MvPolynomial.X (0 : Fin 2) : R)
      let J : Ideal L :=
        Ideal.span ({algebraMap R L (MvPolynomial.X (1 : Fin 2))} : Set L)
      let algebraMapToQuotient : R →+* L ⧸ J :=
        (Ideal.Quotient.mk J).comp (algebraMap R L)
      (ModuleCat.restrictScalars algebraMapToQuotient).obj
        (ModuleCat.of (L ⧸ J) (L ⧸ J)) := sorry

/-- The flattening functor for `Spec(k[x, y])` and the sheaf associated to `module k`. -/
def functor (k : Type u) [Field k] :
    (Over (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))))ᵒᵖ ⥤ Type u :=
  AlgebraicGeometry.Scheme.Modules.Flattening.functor
    (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))))
    (tilde (module k))

/-- Every infinitesimal fiber over `Spec(k[x, y] / (x, y) ^ n)` is inhabited and has at most one
element. -/
theorem infinitesimalFiberIsSingleton (k : Type u) [Field k] (n : ℕ) :
    Nonempty
        ((functor k).obj (op (OverSpec.affine
          (IdealPower.projection (PuncturedAffineSpace.originIdeal (Fin 2) k) n)))) ∧
      ∀ x y : (functor k).obj (op (OverSpec.affine
        (IdealPower.projection (PuncturedAffineSpace.originIdeal (Fin 2) k) n))),
        x = y := sorry

/-- The fiber over the formal completion `Spec(k[[x, y]])` is empty. -/
theorem completionFiberIsEmpty (k : Type u) [Field k] :
    ¬ Nonempty
      ((functor k).obj (op (OverSpec.affine
        (CommRingCat.ofHom coeToMvPowerSeries.ringHom)))) := sorry

/-- If the flattening functor is represented by an algebraic space and every infinitesimal fiber
is inhabited, then its fiber over the power-series completion is inhabited. -/
theorem completionFiberNonempty_of_algebraicSpaceRepresentation
    (k : Type u) [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))))
    (e : X.functorOfPoints ≅ functor k)
    (h : ∀ n : ℕ, Nonempty
      ((functor k).obj (op (OverSpec.affine
        (IdealPower.projection (PuncturedAffineSpace.originIdeal (Fin 2) k) n))))) :
    Nonempty
      ((functor k).obj (op (OverSpec.affine
        (CommRingCat.ofHom coeToMvPowerSeries.ringHom)))) := sorry

/-- The flattening functor is not represented by an algebraic space over `Spec(k[x, y])`. -/
theorem notRepresentableByAlgebraicSpace (k : Type u) [Field k] :
    ¬ ∃ X : AlgebraicSpace (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))),
      Nonempty (X.functorOfPoints ≅ functor k) := sorry

/-- The flattening functor over `Spec(k[x, y])` is not representable by a scheme. -/
theorem noUniversalFlattening (k : Type u) [Field k] :
    ¬ (functor k).IsRepresentable := sorry

end AlgebraicGeometry.Scheme.Flattening.Counterexample
