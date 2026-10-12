/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Function-field adeles of a smooth projective curve

Local completions `K_v` and integers `O_v` at closed points of a geometrically
irreducible smooth projective curve, together with the restricted product
`A = Πʳ_v K_v` and the integral adeles `O = Π_v O_v`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open IsDedekindDomain Matrix
open scoped RestrictedProduct

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/-- The stalk of a smooth curve at a closed point is a discrete valuation ring. -/
instance instIsDiscreteValuationRing_closedPointStalk [Curve X] [Smooth X.hom]
    (v : closedPoints X.left) :
    IsDiscreteValuationRing (X.left.presheaf.stalk v.1) := sorry

/-- The stalk of a smooth curve at a closed point is a Dedekind domain. -/
instance instIsDedekindDomain_closedPointStalk [Curve X] [Smooth X.hom]
    (v : closedPoints X.left) :
    IsDedekindDomain (X.left.presheaf.stalk v.1) := sorry

/-- The height-one prime of the local ring at a closed point of a smooth curve. -/
def place [Curve X] [Smooth X.hom] (v : closedPoints X.left) :
    HeightOneSpectrum (X.left.presheaf.stalk v.1) :=
  IsDiscreteValuationRing.maximalIdeal (X.left.presheaf.stalk v.1)

/-- `place X v` is the maximal ideal of the stalk at `v`. -/
theorem place_asIdeal [Curve X] [Smooth X.hom] (v : closedPoints X.left) :
    (place X v).asIdeal = IsLocalRing.maximalIdeal (X.left.presheaf.stalk v.1) := sorry

/-- The place at a closed point is a nonzero ideal. -/
theorem place_ne_bot [Curve X] [Smooth X.hom] (v : closedPoints X.left) :
    (place X v).asIdeal ≠ ⊥ := sorry

/-- The completion `K_v` of the function field at a closed point. -/
abbrev completion [Curve X] [Smooth X.hom] (v : closedPoints X.left) :=
  (place X v).adicCompletion X.left.functionField

/-- `completion X v` is the adic completion of `k(X)` at `place X v`. -/
theorem completion_eq [Curve X] [Smooth X.hom] (v : closedPoints X.left) :
    completion X v = (place X v).adicCompletion X.left.functionField := sorry

/-- The integer ring `O_v` in the local completion `K_v`. -/
abbrev completionIntegers [Curve X] [Smooth X.hom] (v : closedPoints X.left) :=
  (place X v).adicCompletionIntegers X.left.functionField

/-- Membership in `O_v` is the valuation inequality `Valued.v x ≤ 1`. -/
theorem mem_completionIntegers [Curve X] [Smooth X.hom] (v : closedPoints X.left)
    (x : completion X v) :
    x ∈ completionIntegers X v ↔ Valued.v x ≤ 1 := sorry

/-- The adele ring `A = Πʳ_v K_v` of the function field of `X`. -/
abbrev adeleRing [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :=
  Πʳ v : closedPoints X.left, [completion X v, completionIntegers X v]

/-- `adeleRing X` is the restricted product of the local completions `K_v`. -/
theorem adeleRing_eq [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :
    adeleRing X =
      RestrictedProduct (fun v ↦ completion X v) (fun v ↦ completionIntegers X v)
        Filter.cofinite := sorry

namespace adeleRing

/-- The diagonal embedding of the function field into the adele ring. -/
def algebraMap [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :
    X.left.functionField →+* adeleRing X where
  toFun k := ⟨fun v ↦ Algebra.algebraMap X.left.functionField (completion X v) k, sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The `v`-component of `adeleRing.algebraMap X k` is the local algebra map into `K_v`. -/
theorem algebraMap_apply [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] (k : X.left.functionField)
    (v : closedPoints X.left) :
    algebraMap X k v = Algebra.algebraMap X.left.functionField (completion X v) k := sorry

end adeleRing

/-- The function field acts on the adele ring through the diagonal embedding. -/
instance instAlgebra_adeleRing [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :
    Algebra X.left.functionField (adeleRing X) :=
  (adeleRing.algebraMap X).toAlgebra

/-- The integral adele ring `O = Π_v O_v`. -/
abbrev integerAdeleRing [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :=
  (v : closedPoints X.left) → completionIntegers X v

/-- An integral adele is a family of local integers `O_v`. -/
theorem integerAdeleRing_eq [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :
    integerAdeleRing X = ((v : closedPoints X.left) → completionIntegers X v) := sorry

namespace integerAdeleRing

/-- The inclusion of integral adeles into the restricted product of completions. -/
def toAdeleRing [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :
    integerAdeleRing X →+* adeleRing X where
  toFun x := ⟨fun v ↦ (x v : completion X v), Filter.Eventually.of_forall fun v ↦ SetLike.coe_mem (x v)⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The `v`-component of `toAdeleRing x` is the underlying local integer at `v`. -/
theorem toAdeleRing_apply [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] (x : integerAdeleRing X)
    (v : closedPoints X.left) :
    toAdeleRing X x v = (x v : completion X v) := sorry

end integerAdeleRing

/-- The embedding `GL (Fin 2) K →* GL (Fin 2) A` induced by `K → A`. -/
def functionFieldGL [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :
    GL (Fin 2) X.left.functionField →* GL (Fin 2) (adeleRing X) :=
  GeneralLinearGroup.map (adeleRing.algebraMap X)

/-- `functionFieldGL` is `GeneralLinearGroup.map` along the diagonal embedding. -/
theorem functionFieldGL_apply [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] (γ : GL (Fin 2) X.left.functionField) :
    functionFieldGL X γ = GeneralLinearGroup.map (adeleRing.algebraMap X) γ := sorry

/-- The embedding `GL (Fin 2) O →* GL (Fin 2) A` induced by `O → A`. -/
def integerAdeleGL [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] :
    GL (Fin 2) (integerAdeleRing X) →* GL (Fin 2) (adeleRing X) :=
  GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X)

/-- `integerAdeleGL` is `GeneralLinearGroup.map` along `O → A`. -/
theorem integerAdeleGL_apply [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] (u : GL (Fin 2) (integerAdeleRing X)) :
    integerAdeleGL X u = GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X) u := sorry

/-- The principal adeles, i.e. the image of `K` in `A`. -/
def principalAdeles [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] : AddSubgroup (adeleRing X) :=
  (RingHom.range (adeleRing.algebraMap X)).toAddSubgroup

/-- Membership in the principal adeles is being in the image of `K → A`. -/
theorem mem_principalAdeles [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] (x : adeleRing X) :
    x ∈ principalAdeles X ↔
      ∃ k : X.left.functionField, adeleRing.algebraMap X k = x := sorry

end AlgebraicGeometry.SchemeOverField
