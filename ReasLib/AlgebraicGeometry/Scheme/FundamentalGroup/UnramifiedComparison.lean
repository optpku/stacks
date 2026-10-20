/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Galois
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedExtension
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.FunctionFieldExtension
open AlgebraicGeometry.Scheme.FieldValuedPoint
open AlgebraicGeometry.Scheme.GeometricPoint
open InfiniteGalois

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The residue map from the function field of an integral scheme to the residue field of
its generic point is bijective. -/
theorem functionFieldResidueFieldGenericPoint_bijective (X : Scheme.{u}) [IsIntegral X] :
    Function.Bijective (X.residue (genericPoint X)).hom := sorry

/-- The function-field algebra on the source field of a geometric point lying over
`genericPoint X`, assembled from the generic-point residue map, the residue-field
congruence along the image, and the residue-field embedding of the geometric point. -/
@[reducible] def functionFieldAlgebra_of_genericAlgebraicPoint {X : Scheme.{u}} [IsIntegral X]
    (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    Algebra X.functionField ηbar.K :=
  (X.residue (genericPoint X) ≫ (X.residueFieldCongr h_gen.symm).hom ≫
      ηbar.toFieldValuedPoint.residueFieldHom).hom.toAlgebra

/-- The algebra map of `functionFieldAlgebra_of_genericAlgebraicPoint` is the residue
factorization through `κ(genericPoint X)`. -/
theorem functionFieldAlgebra_of_genericAlgebraicPoint_algebraMap
    {X : Scheme.{u}} [IsIntegral X] (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    (functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen).algebraMap =
      (X.residue (genericPoint X) ≫ (X.residueFieldCongr h_gen.symm).hom ≫
          ηbar.toFieldValuedPoint.residueFieldHom).hom := sorry

/-- The canonical morphism `Spec k(X) ⟶ X` from the spectrum of the function field. -/
def fromSpecFunctionField (X : Scheme.{u}) [IsIntegral X] :
    Spec (.of X.functionField) ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- `fromSpecFunctionField` is the canonical morphism from the spectrum of the stalk at
the generic point. -/
theorem fromSpecFunctionField_eq (X : Scheme.{u}) [IsIntegral X] :
    fromSpecFunctionField X = X.fromSpecStalk (genericPoint X) := sorry

/-- The geometric point of `Spec k(X)` with source field `ηbar.K` associated to an
algebraic geometric point of `X` lying over the generic point. -/
def specFunctionFieldGeometricPoint {X : Scheme.{u}} [IsIntegral X]
    (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    GeometricPoint (Spec (.of X.functionField)) :=
  -- Local instance justification (noncanonical choice): the residue algebra on ηbar.K is this geometric generic point's algebra, not AlgebraicClosure k(X).
  letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
  @specFieldGeometricPoint X.functionField ηbar.K _ _ _ ηbar.isAlgClosed

/-- Postcomposition of `specFunctionFieldGeometricPoint` along `fromSpecFunctionField`
recovers the original geometric point of `X`. -/
theorem specFunctionFieldGeometricPoint_postcomp {X : Scheme.{u}} [IsIntegral X]
    (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    GeometricPoint.map (specFunctionFieldGeometricPoint ηbar h_gen)
        (fromSpecFunctionField X) =
      ηbar := sorry

/-- The algebra structure on `ηbar.K` over `SeparableClosure k(X)` obtained by lifting the
function-field embedding into this algebraic closure. -/
@[reducible] def separableClosureAlgebra_of_genericAlgebraicPoint {X : Scheme.{u}} [IsIntegral X]
    (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    Algebra (SeparableClosure X.functionField) ηbar.K :=
  -- Local instance justification (noncanonical choice): IsSepClosed.lift extends this geometric generic point's residue algebra on ηbar.K, not AlgebraicClosure k(X).
  letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
  (@IsSepClosed.lift X.functionField (SeparableClosure X.functionField) ηbar.K
      _ _ _ _ _ (@IsSepClosed.of_isAlgClosed ηbar.K _ ηbar.isAlgClosed) _).toRingHom.toAlgebra

/-- The separable-closure algebra map on `ηbar.K` extends the named function-field residue
algebra. -/
theorem algebraMap_separableClosure_comp_functionField
    {X : Scheme.{u}} [IsIntegral X] (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    (separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen).algebraMap.comp
        (algebraMap X.functionField (SeparableClosure X.functionField)) =
      (functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen).algebraMap := sorry

/-- The named function-field, separable-closure, and source-field algebras on `ηbar.K` form a
scalar tower. -/
theorem isScalarTower_separableClosure_of_genericAlgebraicPoint
    {X : Scheme.{u}} [IsIntegral X] (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    -- Local instance justification (noncanonical choice): the tower is the one induced by this geometric generic point's residue algebra and its separable-closure lift.
    letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
    -- Local instance justification (noncanonical choice): Ksep acts on ηbar.K through the lift of that residue algebra.
    letI := separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen
    IsScalarTower X.functionField (SeparableClosure X.functionField) ηbar.K := sorry

/-- The named function-field residue algebra of an algebraic geometric generic point is
algebraic. -/
theorem isAlgebraic_functionField_of_genericAlgebraicPoint {X : Scheme.{u}} [IsIntegral X]
    (ηbar : GeometricPoint X)
    (h_alg : @IsAlgClosure _ _ _ _ (ηbar.toFieldValuedPoint.residueFieldHom.hom.toAlgebra) _)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    -- Local instance justification (noncanonical choice): algebraicity is for this geometric generic point's residue algebra on ηbar.K, not an arbitrary K-algebra structure.
    letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
    Algebra.IsAlgebraic X.functionField ηbar.K := sorry

/-- The named separable-closure algebra embeds the maximal unramified extension into `ηbar.K`. -/
theorem algebraMap_maximalUnramifiedExtension_injective {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    Function.Injective
      (((separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen).algebraMap).comp
        (algebraMap (maximalUnramifiedExtension X hX)
          (SeparableClosure X.functionField))) := sorry

/-- The comparison `Gal(Ksep / k(X)) → π₁(X, fromSpecFunctionField ∘ specFunctionFieldGeometricPoint)`
obtained by transporting `galoisToFundamentalGroup` along `fromSpecFunctionField`. -/
def galoisToEtaleFundamentalGroup {X : Scheme.{u}} [IsIntegral X]
    (ηbar : GeometricPoint X)
    (h_alg : @IsAlgClosure _ _ _ _ (ηbar.toFieldValuedPoint.residueFieldHom.hom.toAlgebra) _)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    ContinuousMonoidHom
      Gal(SeparableClosure X.functionField/X.functionField)
      (etaleFundamentalGroup X
        (GeometricPoint.map (specFunctionFieldGeometricPoint ηbar h_gen)
          (fromSpecFunctionField X))) :=
  -- Local instance justification (noncanonical choice): Gal(Ksep/k(X)) → π₁ uses this geometric generic point's residue algebra on ηbar.K, not AlgebraicClosure k(X).
  letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
  -- Local instance justification (noncanonical choice): Ksep acts on ηbar.K through the lift of that residue algebra.
  letI := separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen
  -- Local instance justification (noncanonical choice): the k(X)/Ksep/ηbar.K tower is the one induced by this geometric generic point.
  letI := isScalarTower_separableClosure_of_genericAlgebraicPoint ηbar h_gen
  -- Local instance justification (noncanonical choice): algebraicity of ηbar.K/k(X) is this geometric point's IsAlgebraic, not the abstract algebraic closure.
  letI := isAlgebraic_functionField_of_genericAlgebraicPoint ηbar h_alg h_gen
  (fundamentalGroupMap (fromSpecFunctionField X)
      (specFunctionFieldGeometricPoint ηbar h_gen)).comp
    (@galoisToFundamentalGroup X.functionField ηbar.K (SeparableClosure X.functionField)
      _ _ _ _ _ _ _ ηbar.isAlgClosed _)

namespace FunctionFieldExtension

/-- Finite subextensions of the maximal unramified extension yield finite étale
normalization morphisms. -/
theorem finiteEtaleMorphism_fromNormalization_of_le
    {X : Scheme.{u}} [IsIntegral X] (hX : X.isNormal)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX) :
    finiteEtaleMorphism (map X L).fromNormalization := sorry

end FunctionFieldExtension

/-- Normalization of `X` in a finite subextension of `M`, as a finite étale object. -/
def finiteEtaleNormalization {X : Scheme.{u}} [IsIntegral X] (hX : X.isNormal)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX) :
    FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (map X L).fromNormalization
    (finiteEtaleMorphism_fromNormalization_of_le hX L hL)

/-- The structure morphism of `finiteEtaleNormalization` is the relative normalization. -/
theorem finiteEtaleNormalization_hom {X : Scheme.{u}} [IsIntegral X] (hX : X.isNormal)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX) :
    (finiteEtaleNormalization hX L hL).hom = (map X L).fromNormalization := sorry

/-- The triangle identifying the distinguished `Spec L`-point of the normalization with `ηbar`. -/
theorem distinguishedNormalizationPoint_w {X : Scheme.{u}} [IsIntegral X]
    (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField)) :
    -- Local instance justification (noncanonical choice): the distinguished Spec L-point uses this geometric generic point's residue algebra on ηbar.K.
    letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
    -- Local instance justification (noncanonical choice): L embeds into ηbar.K through the separable-closure lift of that residue algebra.
    letI := separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen
    (Spec.map (CommRingCat.ofHom (algebraMap L ηbar.K)) ≫
          (map X L).toNormalization) ≫
        (map X L).fromNormalization =
      ηbar.hom := sorry

/-- The distinguished `ηbar`-point of the normalization in `L`, induced by the composite
algebra map `L → Ksep → ηbar.K`. -/
def distinguishedNormalizationPoint {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX) :
    (finiteFiber ηbar).obj (finiteEtaleNormalization hX L hL) :=
  -- Local instance justification (noncanonical choice): the distinguished Spec L-point uses this geometric generic point's residue algebra on ηbar.K.
  letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
  -- Local instance justification (noncanonical choice): L embeds into ηbar.K through the separable-closure lift of that residue algebra.
  letI := separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen
  Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap L ηbar.K)) ≫ (map X L).toNormalization)
    (distinguishedNormalizationPoint_w ηbar h_gen L)

/-- The image of the distinguished normalization point under a fiber automorphism. -/
def actedNormalizationMorphism {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX)
    (σ : Aut (finiteFiber ηbar)) :
    Spec (.of ηbar.K) ⟶ (map X L).normalization :=
  (σ.hom.app (finiteEtaleNormalization hX L hL)
      (distinguishedNormalizationPoint hX ηbar h_gen L hL)).left

/-- `actedNormalizationMorphism` is the underlying scheme morphism of the acted fiber point. -/
theorem actedNormalizationMorphism_eq {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX)
    (σ : Aut (finiteFiber ηbar)) :
    actedNormalizationMorphism hX ηbar h_gen L hL σ =
      (σ.hom.app (finiteEtaleNormalization hX L hL)
        (distinguishedNormalizationPoint hX ηbar h_gen L hL)).left := sorry

/-- A factorization of an acted normalization point through `Spec L`. -/
def actedSpecHom {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX)
    (σ : Aut (finiteFiber ηbar)) :
    Spec (.of ηbar.K) ⟶ Spec (.of L) :=
  -- Local instance justification (noncanonical choice): the distinguished Spec L-point uses this geometric generic point's residue algebra on ηbar.K.
  letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
  -- Local instance justification (noncanonical choice): L embeds into ηbar.K through the separable-closure lift of that residue algebra.
  letI := separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen
  -- Local instance justification (noncanonical choice): Hom(Spec ηbar.K, Spec L) is pointed by this geometric generic point's residue embedding, not by an arbitrary K-algebra map.
  letI : Nonempty (Spec (.of ηbar.K) ⟶ Spec (.of L)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap L ηbar.K))⟩
  Function.invFun (fun f : Spec (.of ηbar.K) ⟶ Spec (.of L) =>
      f ≫ (map X L).toNormalization)
    (actedNormalizationMorphism hX ηbar h_gen L hL σ)

/-- `actedSpecHom` factors the acted normalization morphism through `toNormalization`. -/
theorem actedSpecHom_comp_toNormalization {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX)
    (σ : Aut (finiteFiber ηbar)) :
    actedSpecHom hX ηbar h_gen L hL σ ≫ (map X L).toNormalization =
      actedNormalizationMorphism hX ηbar h_gen L hL σ := sorry

/-- Finite-dimensionality of a finite Galois subextension of `M` after lifting to
`SeparableClosure k(X)`. -/
instance finiteDimensional_lift_finGalois {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal)
    (L : FiniteGaloisIntermediateField X.functionField
      (maximalUnramifiedExtension X hX)) :
    FiniteDimensional X.functionField
      (IntermediateField.lift (F := maximalUnramifiedExtension X hX)
        L.toIntermediateField) := sorry

/-- Normality of a finite Galois subextension of `M` after lifting to
`SeparableClosure k(X)`. -/
instance normal_lift_finGalois {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal)
    (L : FiniteGaloisIntermediateField X.functionField
      (maximalUnramifiedExtension X hX)) :
    Normal X.functionField
      (IntermediateField.lift (F := maximalUnramifiedExtension X hX)
        L.toIntermediateField) := sorry

/-- The ring homomorphism `L → ηbar.K` recovered from an acted normalization point. -/
def actedNormalizationRingHom {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX)
    (σ : Aut (finiteFiber ηbar)) :
    L →+* ηbar.K :=
  (Spec.homEquiv (actedSpecHom hX ηbar h_gen L hL σ)).hom

/-- `actedNormalizationRingHom` is the ring homomorphism underlying `actedSpecHom`. -/
theorem actedNormalizationRingHom_eq {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX)
    (σ : Aut (finiteFiber ηbar)) :
    actedNormalizationRingHom hX ηbar h_gen L hL σ =
      (Spec.homEquiv (actedSpecHom hX ηbar h_gen L hL σ)).hom := sorry

/-- Restriction of a fiber automorphism to a finite Galois subextension of `M`, as an
element of `Gal(L / k(X))`. -/
def fiberAutToFinGalois {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (σ : Aut (finiteFiber ηbar))
    (L : FiniteGaloisIntermediateField X.functionField
      (maximalUnramifiedExtension X hX)) :
    Gal(L/X.functionField) :=
  -- Local instance justification (noncanonical choice): the residue algebra on ηbar.K is this geometric generic point's algebra.
  letI := functionFieldAlgebra_of_genericAlgebraicPoint ηbar h_gen
  -- Local instance justification (noncanonical choice): Ksep acts on ηbar.K through the lift of that residue algebra.
  letI := separableClosureAlgebra_of_genericAlgebraicPoint ηbar h_gen
  let Lsep : IntermediateField X.functionField (SeparableClosure X.functionField) :=
    IntermediateField.lift (F := maximalUnramifiedExtension X hX) L.toIntermediateField
  let hL : Lsep ≤ maximalUnramifiedExtension X hX := IntermediateField.lift_le _
  let φ := actedNormalizationRingHom hX ηbar h_gen Lsep hL σ
  let ψ : Lsep →ₐ[X.functionField] SeparableClosure X.functionField :=
    { toFun := fun x =>
        Function.invFun
          (algebraMap (SeparableClosure X.functionField) ηbar.K) (φ x)
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }
  let e : Gal(Lsep / X.functionField) :=
    (AlgHom.equivFieldRange ψ).trans
      (IntermediateField.equivOfEq (AlgHom.fieldRange_of_normal ψ))
  (IntermediateField.liftAlgEquiv L.toIntermediateField).trans e |>.trans
    (IntermediateField.liftAlgEquiv L.toIntermediateField).symm

/-- The identity fiber automorphism acts as the identity on each finite Galois
subextension of `M`. -/
theorem fiberAutToFinGalois_one {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (L : FiniteGaloisIntermediateField X.functionField
      (maximalUnramifiedExtension X hX)) :
    fiberAutToFinGalois hX ηbar h_gen 1 L = 1 := sorry

/-- The comparison homomorphism `π₁(X, ηbar) → Gal(M / k(X))` given by the action of a
fiber automorphism on finite étale normalizations of finite subextensions of `M`. -/
def etaleFundamentalGroupToUnramifiedGalois {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_alg : @IsAlgClosure _ _ _ _ (ηbar.toFieldValuedPoint.residueFieldHom.hom.toAlgebra) _)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    ContinuousMonoidHom (etaleFundamentalGroup X ηbar)
      Gal(maximalUnramifiedExtension X hX/X.functionField) where
  toFun σ :=
    -- Local instance justification (noncanonical choice): algebraicity of ηbar.K/k(X) is this geometric point's IsAlgebraic.
    letI := isAlgebraic_functionField_of_genericAlgebraicPoint ηbar h_alg h_gen
    limitToAlgEquiv
      { val := fun L =>
          fiberAutToFinGalois hX ηbar h_gen σ L.unop
        property := fun _ => sorry }
  map_one' := sorry
  map_mul' := sorry
  continuous_toFun := sorry

/-- The comparison homomorphism factors `galoisToEtaleFundamentalGroup` as restriction
onto the maximal unramified extension, after identifying the postcomposed geometric
point with `ηbar`. -/
theorem etaleFundamentalGroupToUnramifiedGalois_comp {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_alg : @IsAlgClosure _ _ _ _ (ηbar.toFieldValuedPoint.residueFieldHom.hom.toAlgebra) _)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    (etaleFundamentalGroupToUnramifiedGalois hX ηbar h_alg h_gen).toMonoidHom.comp
        (specFunctionFieldGeometricPoint_postcomp ηbar h_gen ▸
          (galoisToEtaleFundamentalGroup ηbar h_alg h_gen).toMonoidHom) =
      AlgEquiv.restrictNormalHom (maximalUnramifiedExtension X hX) := sorry

/-- A continuous monoid homomorphism `π₁(X, ηbar) → Gal(M / k(X))` making the
restriction triangle commute is unique. -/
theorem etaleFundamentalGroupToUnramifiedGalois_unique {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (ηbar : GeometricPoint X)
    (h_alg : @IsAlgClosure _ _ _ _ (ηbar.toFieldValuedPoint.residueFieldHom.hom.toAlgebra) _)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X)
    (e e' : ContinuousMonoidHom (etaleFundamentalGroup X ηbar)
      Gal(maximalUnramifiedExtension X hX/X.functionField))
    (he : e.toMonoidHom.comp
        (specFunctionFieldGeometricPoint_postcomp ηbar h_gen ▸
          (galoisToEtaleFundamentalGroup ηbar h_alg h_gen).toMonoidHom) =
      AlgEquiv.restrictNormalHom (maximalUnramifiedExtension X hX))
    (he' : e'.toMonoidHom.comp
        (specFunctionFieldGeometricPoint_postcomp ηbar h_gen ▸
          (galoisToEtaleFundamentalGroup ηbar h_alg h_gen).toMonoidHom) =
      AlgEquiv.restrictNormalHom (maximalUnramifiedExtension X hX)) :
    e = e' := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FunctionFieldExtension

/-- Finite subextensions of the maximal unramified extension have finite étale
normalization over a normal integral scheme. -/
theorem le_maximalUnramifiedExtension_fromNormalization_finiteEtale
    {X : Scheme.{u}} [IsIntegral X] (hX : X.isNormal)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L]
    (hL : L ≤ maximalUnramifiedExtension X hX) :
    IsFinite (map X L).fromNormalization ∧ Etale (map X L).fromNormalization := sorry

/-- The maximal unramified extension is maximal among extensions of the function field
inside `SeparableClosure k(X)` whose finite subextensions have finite étale
normalization. -/
theorem maximalUnramifiedExtension_is_maximal_finiteEtale {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal)
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    (hL : ∀ (E : IntermediateField X.functionField (SeparableClosure X.functionField))
      [FiniteDimensional X.functionField E], E ≤ L →
        IsFinite (map X E).fromNormalization ∧ Etale (map X E).fromNormalization) :
    L ≤ maximalUnramifiedExtension X hX := sorry

end AlgebraicGeometry.Scheme.FunctionFieldExtension

namespace AlgebraicGeometry.Scheme

/-- The étale fundamental group at an algebraic geometric generic point is homeomorphic to
the Galois group of the maximal extension with finite étale normalizations. -/
theorem etaleFundamentalGroup_isHomeomorph_unramifiedGalois
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] (hX : X.isNormal)
    (ηbar : GeometricPoint X)
    (h_alg : @IsAlgClosure _ _ _ _ (ηbar.toFieldValuedPoint.residueFieldHom.hom.toAlgebra) _)
    (h_gen : ηbar.toFieldValuedPoint.image = genericPoint X) :
    IsHomeomorph (etaleFundamentalGroupToUnramifiedGalois hX ηbar h_alg h_gen) := sorry

end AlgebraicGeometry.Scheme
