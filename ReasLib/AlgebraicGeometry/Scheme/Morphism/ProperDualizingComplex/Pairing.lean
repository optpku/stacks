/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CoherentBounded
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded Scheme.Hom
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

/-- The degree-zero trace associated to the identity of the proper dualizing complex. -/
noncomputable def trace
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    cohomologyOverField f (properDualizingComplex f) 0 ⟶ fieldObject k :=
  extComparison f 0 (properDualizingComplex f)
    (ShiftedHom.mk₀ 0 rfl (𝟙 (properDualizingComplex f)))

/-- The trace is the proper-duality comparison applied to the degree-zero identity class. -/
theorem trace_eq_extComparison_identity
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    trace f = extComparison f 0 (properDualizingComplex f)
      (ShiftedHom.mk₀ 0 rfl (𝟙 (properDualizingComplex f))) := sorry

/-- After an explicit identification of the affine-derived field object with `k`, the identity
of the proper dualizing complex defines the trace `H⁰(X, ω) ⟶ k`. -/
noncomputable def traceWith
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    cohomologyOverField f (properDualizingComplex f) 0 ⟶ ModuleCat.of k k :=
  trace f ≫ e.hom

/-- The `k`-valued trace is the canonical trace followed by the chosen field-object
identification. -/
theorem traceWith_eq
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    traceWith e f = trace f ≫ e.hom := sorry

/-- Lift an ambient derived `Ext` class uniquely to the full subcategory of derived
quasicoherent objects. -/
noncomputable def ambientExtLift
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X)
    (α : DerivedExt.value f K.obj (properDualizingComplex f).obj i) :
    Ext⁽i⁾(K, properDualizingComplex f) :=
  (DerivedQCoh.inclusion X).preimage
    (α ≫ ((DerivedQCoh.inclusion X).commShiftIso i).inv.app
      (properDualizingComplex f))

/-- Mapping `ambientExtLift` back to the ambient derived category recovers its input. -/
theorem ambientExtLift_map
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X)
    (α : DerivedExt.value f K.obj (properDualizingComplex f).obj i) :
    ShiftedHom.map (ambientExtLift f i K α) (DerivedQCoh.inclusion X) = α := sorry

/-- An ambient derived `Ext` class has at most one lift to derived quasicoherent objects. -/
theorem ambientExtLift_unique
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X)
    (α : DerivedExt.value f K.obj (properDualizingComplex f).obj i)
    (g : Ext⁽i⁾(K, properDualizingComplex f))
    (hg : ShiftedHom.map g (DerivedQCoh.inclusion X) = α) :
    ambientExtLift f i K α = g := sorry

/-- Proper cohomology of `K[-i]` in degree zero, identified with proper cohomology of `K`
in degree `-i`. -/
noncomputable def cohomologyNegShiftIso
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X) :
    cohomologyOverField f (K⟦-i⟧) 0 ≅ cohomologyOverField f K (-i) :=
  cohomologyShiftIso f 0 (-i) K ≪≫
    eqToIso (congrArg (cohomologyOverField f K)
      ((congrArg Neg.neg (Int.zero_sub (-i))).trans (Int.neg_neg (-i))))

/-- Additivity of the degree-`i` trace pairing on ambient derived `Ext` classes. -/
theorem pairingWith_map_add
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X)
    (α β : DerivedExt.value f K.obj (properDualizingComplex f).obj i) :
    ((extComparison f i K (ambientExtLift f i K (α + β))) ≫ e.hom).hom =
      ((extComparison f i K (ambientExtLift f i K α)) ≫ e.hom).hom +
        ((extComparison f i K (ambientExtLift f i K β)) ≫ e.hom).hom := sorry

/-- Homogeneity of the degree-`i` trace pairing on ambient derived `Ext` classes. -/
theorem pairingWith_map_smul
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X)
    (r : k) (α : DerivedExt.value f K.obj (properDualizingComplex f).obj i) :
    ((extComparison f i K (ambientExtLift f i K (r • α))) ≫ e.hom).hom =
      r • ((extComparison f i K (ambientExtLift f i K α)) ≫ e.hom).hom := sorry

/-- The degree-`i` derived `Ext` module pairs linearly with `H⁻ⁱ(X, K)` by the proper-duality
comparison and the chosen identification of its target with `k`. -/
noncomputable def pairingWith
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X) :
    DerivedExt.value f K.obj (properDualizingComplex f).obj i →ₗ[k]
      Module.Dual k (cohomologyOverField f K (-i)) where
  toFun α := ((extComparison f i K (ambientExtLift f i K α)) ≫ e.hom).hom
  map_add' α β := pairingWith_map_add e f i K α β
  map_smul' r α := pairingWith_map_smul e f i K r α

/-- Evaluating `pairingWith` is evaluation of the proper-duality comparison followed by
the chosen identification with `k`. -/
theorem pairingWith_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X)
    (α : DerivedExt.value f K.obj (properDualizingComplex f).obj i) :
    pairingWith e f i K α =
      ((extComparison f i K (ambientExtLift f i K α)) ≫ e.hom).hom := sorry

/-- The value of the degree-`i` pairing on `(α, β)` is `t (α (β))`, after identifying
`β ∈ H⁻ⁱ(X, K)` with degree-zero cohomology of `K[-i]`. -/
theorem pairingWith_trace
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X)
    (α : DerivedExt.value f K.obj (properDualizingComplex f).obj i)
    (β : cohomologyOverField f K (-i)) :
    pairingWith e f i K α β =
      traceWith e f
        (cohomologyOverFieldMap f
          (ShiftedHom.sourceShiftEquiv K (properDualizingComplex f) i
            (ambientExtLift f i K α)) 0
          ((cohomologyNegShiftIso f i K).inv β)) := sorry

/-- For arbitrary derived quasicoherent `K`, the degree-`i` pairing identifies `Extⁱ_X(K, ω)`
with the `k`-linear dual of `H⁻ⁱ(X, K)`. -/
theorem pairingWith_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X) :
    Function.Bijective (pairingWith e f i K) := sorry

/-- Every proper-cohomology group of a bounded complex with coherent cohomology is
finite-dimensional over the ground field. -/
instance boundedCohomologyFinite
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) (j : ℤ) :
    FiniteDimensional k
      (cohomologyOverField f
        ((@coherentBoundedToDerivedQCoh X
          (LocallyOfFiniteType.isLocallyNoetherian f)).obj K) j) := sorry

/-- Every derived `Ext` group from a bounded complex with coherent cohomology to the proper
dualizing complex is finite-dimensional over the ground field. -/
instance boundedExtFinite
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) (i : ℤ) :
    FiniteDimensional k
      (DerivedExt.value f
        ((@coherentBoundedToDerivedQCoh X
          (LocallyOfFiniteType.isLocallyNoetherian f)).obj K).obj
        (properDualizingComplex f).obj i) := sorry

/-- For a bounded complex with coherent cohomology, the degree-`i` trace pairing is perfect
in the usual finite-dimensional sense. -/
instance pairingWith_isPerfPair
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) (i : ℤ) :
    LinearMap.IsPerfPair
      (pairingWith e f i
        ((@coherentBoundedToDerivedQCoh X
          (LocallyOfFiniteType.isLocallyNoetherian f)).obj K)) := sorry


/-- Naturality of the `k`-valued proper-duality pairing for a morphism of derived
quasicoherent objects. -/
theorem pairingWith_naturality
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) {K L : DerivedQCoh X} (a : K ⟶ L) :
    (pairingWith e f i K).comp
        (((DerivedExt.bifunctor f i).map
          ((DerivedQCoh.inclusion X).map a).op).app
            (properDualizingComplex f).obj).hom =
      (cohomologyOverFieldMap f a (-i)).hom.dualMap.comp
        (pairingWith e f i L) := sorry

/-- Naturality of the `k`-valued proper-duality pairing for a morphism of quasicoherent
modules: pullback of derived `Ext` is the `k`-linear dual of the induced map on proper
cohomology. -/
theorem pairingWith_module_naturality
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) {F G : QCoh X} (φ : F ⟶ G) :
    (pairingWith e f i (moduleObject F)).comp
        (((DerivedExt.bifunctor f i).map
          ((DerivedQCoh.inclusion X).map (moduleObjectMap φ)).op).app
            (properDualizingComplex f).obj).hom =
      (cohomologyOverFieldMap f (moduleObjectMap φ) (-i)).hom.dualMap.comp
        (pairingWith e f i (moduleObject G)) := sorry

/-- Pointwise evaluation of the quasicoherent-module naturality of the `k`-valued
proper-duality pairing. -/
theorem pairingWith_module_naturality_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) {F G : QCoh X} (φ : F ⟶ G)
    (α : DerivedExt.value f (moduleObject G).obj
      (properDualizingComplex f).obj i)
    (β : cohomologyOverField f (moduleObject F) (-i)) :
    pairingWith e f i (moduleObject F)
        ((((DerivedExt.bifunctor f i).map
          ((DerivedQCoh.inclusion X).map (moduleObjectMap φ)).op).app
            (properDualizingComplex f).obj).hom α) β =
      pairingWith e f i (moduleObject G) α
        ((cohomologyOverFieldMap f (moduleObjectMap φ) (-i)).hom β) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
