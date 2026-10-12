/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Lean

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import stacks_project.Chap111.Exercise_111_27_7_ReesProj

/-!
# Blowup of the affine plane at the origin

The standard blowup `b : X ⟶ Spec(k[x, y])` of the affine plane in the origin,
realized as `Proj` of the Rees algebra of `m = (x, y)`, together with the
scheme-theoretic fibre `E` over the origin and the restriction of the ideal
sheaf of `E`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.AffinePlaneBlowup

/-- The polynomial coordinate ring `k[x, y]` of the affine plane. -/
abbrev coordinateRing (k : Type u) [Field k] : Type u :=
  PuncturedAffineSpace.coordinateRing (Fin 2) k

/-- The affine plane `A²_k = Spec(k[x, y])`. -/
abbrev affinePlane (k : Type u) [Field k] : Scheme.{u} :=
  PuncturedAffineSpace.coordinateSpectrum (Fin 2) k

/-- The origin ideal `m = (x, y)` in `k[x, y]`. -/
abbrev originIdeal (k : Type u) [Field k] : Ideal (coordinateRing k) :=
  PuncturedAffineSpace.originIdeal (Fin 2) k

/-- The origin of `A²_k`, as the prime spectrum point cut out by `m`. -/
abbrev origin (k : Type u) [Field k] : affinePlane k :=
  PuncturedAffineSpace.coordinateOrigin (Fin 2) k

/-- The origin ideal is the span of the two coordinate functions `X 0` and `X 1`. -/
theorem originIdeal_eq_span (k : Type u) [Field k] :
    originIdeal k = Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1} := sorry

/-- The blowup `X = Proj(⨁_{n ≥ 0} m^n)` of the affine plane in the origin. -/
abbrev scheme (k : Type u) [Field k] : Scheme.{u} :=
  Proj (ReesProj.grading (originIdeal k))

/-- The blowup morphism `b : X ⟶ A²_k`. -/
abbrev hom (k : Type u) [Field k] : scheme k ⟶ affinePlane k :=
  ReesProj.toSpec (originIdeal k)

/-- The scheme-theoretic fibre `E` of `b` over the origin. -/
abbrev exceptionalFiber (k : Type u) [Field k] : Scheme.{u} :=
  (hom k).fiber (origin k)

/-- The closed immersion of the exceptional fibre into the blowup. -/
abbrev exceptionalι (k : Type u) [Field k] : exceptionalFiber k ⟶ scheme k :=
  (hom k).fiberι (origin k)

/-- The ideal sheaf `𝒪_X(-E)` of the exceptional fibre in the blowup. -/
abbrev negSheaf (k : Type u) [Field k] : (scheme k).Modules :=
  RingedSpace.Hom.idealSheaf (exceptionalι k).toShHom

/-- The restriction `O_X(-E)|_E` of the ideal sheaf of the exceptional fibre. -/
abbrev restriction (k : Type u) [Field k] : (exceptionalFiber k).Modules :=
  (Scheme.Modules.pullback (exceptionalι k)).obj (negSheaf k)

/-- The restriction of `𝒪_X(-E)` to `E` is isomorphic to the conormal sheaf of the exceptional
immersion, rather than equal to the sheafified kernel-cotangent construction. -/
theorem restriction_isIsomorphic_conormal (k : Type u) [Field k] :
    IsIsomorphic (restriction k) (Scheme.Hom.conormalSheaf (exceptionalι k)) := sorry

/-- The residue field of the origin ideal is canonically identified with `k`. -/
def originIdealResidueFieldEquiv (k : Type u) [Field k] :
    (originIdeal k).ResidueField ≃+* k :=
  (RingEquiv.ofBijective
      (algebraMap (coordinateRing k ⧸ originIdeal k) (originIdeal k).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (originIdeal k))).symm.trans
    ((PuncturedAffineSpace.evalAtOrigin (Fin 2) k).quotientKerEquivOfSurjective
      (PuncturedAffineSpace.evalAtOrigin_surjective (Fin 2) k))

/-- The residue field of the origin point of `A²_k` is canonically `k`. -/
def originResidueFieldIso (k : Type u) [Field k] :
    (affinePlane k).residueField (origin k) ≅ CommRingCat.of k :=
  Scheme.Spec.residueFieldIso (.of (coordinateRing k)) (origin k) ≪≫
    (originIdealResidueFieldEquiv k).toCommRingCatIso

/-- The structure morphism of the exceptional fibre over `Spec k`. -/
abbrev exceptionalToSpec (k : Type u) [Field k] :
    exceptionalFiber k ⟶ Spec (CommRingCat.of k) :=
  (hom k).fiberToSpecResidueField (origin k) ≫ Spec.map (originResidueFieldIso k).inv

/-- The exceptional fibre is proper over `Spec k`. -/
instance exceptionalToSpec_isProper (k : Type u) [Field k] :
    IsProper (exceptionalToSpec k) := sorry

/-- The exceptional fibre has topological Krull dimension at most one. -/
theorem exceptionalFiber_topologicalKrullDim_le_one (k : Type u) [Field k] :
    topologicalKrullDim (exceptionalFiber k) ≤ 1 := sorry

/-- The restriction `O_X(-E)|_E` is an invertible sheaf on the exceptional fibre. -/
instance restriction_isInvertible (k : Type u) [Field k] :
    Scheme.Modules.Invertible (restriction k) := sorry

end AlgebraicGeometry.AffinePlaneBlowup


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
