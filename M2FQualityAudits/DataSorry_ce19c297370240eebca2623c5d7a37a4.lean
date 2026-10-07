module

import Lean

public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap67.Definition_67_47_3_RationalMap

/-!
# The ring of rational functions on an algebraic space

The affine line `𝔸¹_S` is a ring object over `S`. Rational functions on an algebraic space
`X` over `S` are rational maps `X ⤏ 𝔸¹_S`, and they inherit addition and multiplication from
this ring-object structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TypeCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine line over `S`, as a scheme over `S`. -/
def affineLineOver (S : Scheme.{u}) : Over S :=
  Over.mk (𝔸(PUnit.{u + 1}; S) ↘ S)

/-- The affine line `𝔸¹_S`, as an algebraic space over `S`. -/
def affineLine (S : Scheme.{u}) : AlgebraicSpace S :=
  ofOver (affineLineOver S)

/-- The functor of points of `affineLine S` is the Yoneda embedding of the affine line over `S`. -/
theorem affineLine_functorOfPoints (S : Scheme.{u}) :
    (affineLine S).functorOfPoints = yoneda.obj (affineLineOver S) :=
  sorry

/-- The global section of a morphism over `S` into the affine line, extracted from the standard
coordinate. -/
def coordHom {S : Scheme.{u}} {T : Over S} (φ : T ⟶ affineLineOver S) : Γ(T.left, ⊤) :=
  φ.left.appTop (AffineSpace.coord S PUnit.unit)

/-- The morphism over `S` into the affine line classified by a global section. -/
def homOfCoord {S : Scheme.{u}} (T : Over S) (a : Γ(T.left, ⊤)) : T ⟶ affineLineOver S :=
  Over.homMk (AffineSpace.homOfVector T.hom (fun _ : PUnit.{u + 1} ↦ a))
    (AffineSpace.homOfVector_over T.hom (fun _ : PUnit.{u + 1} ↦ a))

/-- Evaluating the morphism associated to a section recovers that section. -/
theorem coordHom_homOfCoord {S : Scheme.{u}} (T : Over S) (a : Γ(T.left, ⊤)) :
    coordHom (homOfCoord T a) = a :=
  sorry

/-- The morphism associated to the coordinate of a map to the affine line recovers that map. -/
theorem homOfCoord_coordHom {S : Scheme.{u}} {T : Over S} (φ : T ⟶ affineLineOver S) :
    homOfCoord T (coordHom φ) = φ :=
  sorry

variable {S : Scheme.{u}}

/-- Pointwise addition of morphisms into the affine line, induced by addition of coordinates. -/
def homAdd {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) : X ⟶ affineLine S where
  app T := ofHom fun x ↦
    homOfCoord T.unop (coordHom (f.app T x) + coordHom (g.app T x))
  naturality := sorry

/-- Pointwise multiplication of morphisms into the affine line, induced by multiplication of
coordinates. -/
def homMul {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) : X ⟶ affineLine S where
  app T := ofHom fun x ↦
    homOfCoord T.unop (coordHom (f.app T x) * coordHom (g.app T x))
  naturality := sorry

/-- The zero morphism into the affine line, classified by the zero section. -/
def homZero (X : AlgebraicSpace S) : X ⟶ affineLine S where
  app T := ofHom fun _ ↦ homOfCoord T.unop 0
  naturality := sorry

/-- The unit morphism into the affine line, classified by the unit section. -/
def homOne (X : AlgebraicSpace S) : X ⟶ affineLine S where
  app T := ofHom fun _ ↦ homOfCoord T.unop 1
  naturality := sorry

/-- Pointwise negation of morphisms into the affine line. -/
def homNeg {X : AlgebraicSpace S} (f : X ⟶ affineLine S) : X ⟶ affineLine S where
  app T := ofHom fun x ↦ homOfCoord T.unop (-coordHom (f.app T x))
  naturality := sorry

/-- The component of `homAdd` is the morphism classified by the sum of coordinates. -/
theorem homAdd_app {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homAdd f g).app T x = homOfCoord T.unop (coordHom (f.app T x) + coordHom (g.app T x)) :=
  sorry

/-- The component of `homMul` is the morphism classified by the product of coordinates. -/
theorem homMul_app {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homMul f g).app T x = homOfCoord T.unop (coordHom (f.app T x) * coordHom (g.app T x)) :=
  sorry

/-- The component of `homZero` is the morphism classified by the zero section. -/
theorem homZero_app (X : AlgebraicSpace S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homZero X).app T x = homOfCoord T.unop 0 :=
  sorry

/-- The component of `homOne` is the morphism classified by the unit section. -/
theorem homOne_app (X : AlgebraicSpace S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homOne X).app T x = homOfCoord T.unop 1 :=
  sorry

/-- The component of `homNeg` is the morphism classified by the negated coordinate. -/
theorem homNeg_app {X : AlgebraicSpace S} (f : X ⟶ affineLine S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (homNeg f).app T x = homOfCoord T.unop (-coordHom (f.app T x)) :=
  sorry

/-- Addition of morphisms into the affine line. -/
instance instAddHomAffineLine {X : AlgebraicSpace S} : Add (X ⟶ affineLine S) where
  add := homAdd

/-- Multiplication of morphisms into the affine line. -/
instance instMulHomAffineLine {X : AlgebraicSpace S} : Mul (X ⟶ affineLine S) where
  mul := homMul

/-- Negation of morphisms into the affine line. -/
instance instNegHomAffineLine {X : AlgebraicSpace S} : Neg (X ⟶ affineLine S) where
  neg := homNeg

/-- The zero morphism into the affine line. -/
instance instZeroHomAffineLine {X : AlgebraicSpace S} : Zero (X ⟶ affineLine S) where
  zero := homZero X

/-- The unit morphism into the affine line. -/
instance instOneHomAffineLine {X : AlgebraicSpace S} : One (X ⟶ affineLine S) where
  one := homOne X

/-- Morphisms from an algebraic space to the affine line form a commutative ring, with operations
induced by the ring-object structure of `𝔸¹_S`. -/
instance instCommRingHomAffineLine {X : AlgebraicSpace S} : CommRing (X ⟶ affineLine S) :=
  CommRing.ofMinimalAxioms sorry sorry sorry sorry sorry sorry sorry

namespace PartialMap

/-- Addition of partial maps into the affine line, by restricting to the fibre product of the
domains and adding the resulting morphisms. -/
def add {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    PartialMap X (affineLine S) where
  domain := domainInfSite f.domain g.domain
  dense_domain := isDense_domainInfHom f.dense_domain g.dense_domain
  hom := homAdd (domainInfFst f.domain.hom g.domain.hom ≫ f.hom)
      (domainInfSnd f.domain.hom g.domain.hom ≫ g.hom)

/-- Multiplication of partial maps into the affine line, by restricting to the fibre product of
the domains and multiplying the resulting morphisms. -/
def mul {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    PartialMap X (affineLine S) where
  domain := domainInfSite f.domain g.domain
  dense_domain := isDense_domainInfHom f.dense_domain g.dense_domain
  hom := homMul (domainInfFst f.domain.hom g.domain.hom ≫ f.hom)
      (domainInfSnd f.domain.hom g.domain.hom ≫ g.hom)

/-- Negation of a partial map into the affine line. -/
def neg {X : AlgebraicSpace S} (f : PartialMap X (affineLine S)) :
    PartialMap X (affineLine S) where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := homNeg f.hom

/-- Addition of partial maps into the affine line respects equivalence. -/
theorem add_equiv {X : AlgebraicSpace S} {f₁ f₂ g₁ g₂ : PartialMap X (affineLine S)}
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) : (f₁.add g₁).equiv (f₂.add g₂) :=
  sorry

/-- Multiplication of partial maps into the affine line respects equivalence. -/
theorem mul_equiv {X : AlgebraicSpace S} {f₁ f₂ g₁ g₂ : PartialMap X (affineLine S)}
    (hf : f₁.equiv f₂) (hg : g₁.equiv g₂) : (f₁.mul g₁).equiv (f₂.mul g₂) :=
  sorry

/-- Negation of partial maps into the affine line respects equivalence. -/
theorem neg_equiv {X : AlgebraicSpace S} {f g : PartialMap X (affineLine S)} (hf : f.equiv g) :
    f.neg.equiv g.neg :=
  sorry

end PartialMap

/-- A rational function on an algebraic space `X` over `S` is a rational map from `X` to the
affine line over `S`. -/
abbrev RationalFunction (X : AlgebraicSpace S) :=
  X.RationalMap (affineLine S)

/-- The type of rational functions is the type of rational maps to the affine line. -/
theorem RationalFunction.eq_rationalMap (X : AlgebraicSpace S) :
    RationalFunction X = X.RationalMap (affineLine S) :=
  sorry

/-- Addition of rational functions, by adding dense-open representatives. -/
instance instAddRationalFunction {X : AlgebraicSpace S} : Add (RationalFunction X) where
  add := Quotient.lift₂ (fun f g ↦ (f.add g).toRationalMap) sorry

/-- Multiplication of rational functions, by multiplying dense-open representatives. -/
instance instMulRationalFunction {X : AlgebraicSpace S} : Mul (RationalFunction X) where
  mul := Quotient.lift₂ (fun f g ↦ (f.mul g).toRationalMap) sorry

/-- Negation of rational functions. -/
instance instNegRationalFunction {X : AlgebraicSpace S} : Neg (RationalFunction X) where
  neg := Quotient.lift (fun f ↦ f.neg.toRationalMap) sorry

/-- The zero rational function. -/
instance instZeroRationalFunction {X : AlgebraicSpace S} : Zero (RationalFunction X) where
  zero := (PartialMap.ofHom (homZero X)).toRationalMap

/-- The unit rational function. -/
instance instOneRationalFunction {X : AlgebraicSpace S} : One (RationalFunction X) where
  one := (PartialMap.ofHom (homOne X)).toRationalMap

/-- Rational functions on an algebraic space form a commutative ring, with addition and
multiplication induced by the ring-object structure of `𝔸¹_S`. -/
instance instCommRingRationalFunction {X : AlgebraicSpace S} : CommRing (RationalFunction X) :=
  CommRing.ofMinimalAxioms sorry sorry sorry sorry sorry sorry sorry

/-- The ring of rational functions on an algebraic space `X`. -/
abbrev rationalFunctionRing (X : AlgebraicSpace S) : CommRingCat.{u + 1} :=
  CommRingCat.of (RationalFunction X)

/-- The ring of rational functions is the commutative ring of rational maps to the affine line. -/
theorem rationalFunctionRing_def (X : AlgebraicSpace S) :
    rationalFunctionRing X = CommRingCat.of (RationalFunction X) :=
  sorry

/-- Addition of rational functions is represented by addition of partial maps on a common dense
open. -/
theorem add_toRationalMap {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    f.toRationalMap + g.toRationalMap = (f.add g).toRationalMap :=
  sorry

/-- Multiplication of rational functions is represented by multiplication of partial maps on a
common dense open. -/
theorem mul_toRationalMap {X : AlgebraicSpace S} (f g : PartialMap X (affineLine S)) :
    f.toRationalMap * g.toRationalMap = (f.mul g).toRationalMap :=
  sorry

end AlgebraicGeometry.AlgebraicSpace


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
