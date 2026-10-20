module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Finite.Extension
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.DegreeExtension
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap58.Lemma_58_6_3_GaloisFiber
public import stacks_project.Chap58.Remark_58_6_4_GaloisAction
public import stacks_project.Chap58.Theorem_58_6_2_Fiber
public import stacks_project.Chap58.Theorem_58_6_2_InducedHom
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»

/-!
# Finite-field degree extensions of `hatZ`

The arithmetic geometric example of a profinite degree extension uses
`arithmeticToGalois` followed by a geometric-Frobenius-normalized map
`π₁(Spec k) ⟶ hatZ`. Its finite quotient coordinates are evaluated on finite-field covers,
and its field and fiber inverses are recovered from actual affine coordinates.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.SchemeOverField
open scoped Topology

universe u

namespace ProfiniteGrp.DegreeExtension

/-- The canonical algebraic-closure geometric point of `Spec k`. -/
noncomputable abbrev specGaloisGeometricPoint (k : Type u) [Field k] :
    GeometricPoint (Spec (CommRingCat.of k)) :=
  specFieldGeometricPoint k (AlgebraicClosure k)

/-- The ring homomorphism `k →+* s.K` induced by a geometric point of `Spec k`. -/
noncomputable def specGeometricPointRingHom {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) : k →+* s.K :=
  CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop s.hom ≫ (Scheme.ΓSpecIso (CommRingCat.of s.K)).hom

/-- The algebra structure on the source field of a geometric point of `Spec k`. -/
noncomputable instance algebra_specGeometricPoint {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) : Algebra k s.K :=
  (specGeometricPointRingHom s).toAlgebra

/-- A geometric point of `Spec k` has algebraically closed source field. -/
instance isAlgClosed_specGeometricPoint {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) : IsAlgClosed s.K :=
  s.isAlgClosed

/-- Unfolding of `specGeometricPointRingHom` through global sections of the spectra. -/
theorem specGeometricPointRingHom_spec {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    specGeometricPointRingHom s =
      CommRingCat.Hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          Scheme.Hom.appTop s.hom ≫ (Scheme.ΓSpecIso (CommRingCat.of s.K)).hom) :=
  sorry

/-- The comparison homomorphism `k̄ → s.K` over `k` used to identify finite étale fibers. -/
noncomputable def specGeometricPointLift {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    AlgebraicClosure k →ₐ[k] s.K :=
  IsAlgClosed.lift

/-- Unfolding of `specGeometricPointLift` as `IsAlgClosed.lift`. -/
theorem specGeometricPointLift_spec {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    specGeometricPointLift s = IsAlgClosed.lift :=
  sorry

/-- Forward comparison of finite étale fibers at the canonical algebraic-closure point
and at a general geometric point of `Spec k`. -/
noncomputable def specFieldFiberToPointFiber {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k)))
    (y : finiteEtaleFiberObj (specGaloisGeometricPoint k) Y) :
    finiteEtaleFiberObj s Y :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (specGeometricPointLift s).toRingHom) ≫ y.left)
    (w := sorry)

/-- Finite étale geometric fibers over `Spec k` are identified with the canonical
algebraic-closure fiber. -/
theorem specFieldFiberToPointFiber_bijective {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    Function.Bijective (specFieldFiberToPointFiber s Y) :=
  sorry

/-- The specified embedding of an algebraic closure has algebraic values. -/
theorem specGeometricPointLift_mem_algebraicClosure {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) (x : AlgebraicClosure k) :
    specGeometricPointLift s x ∈ algebraicClosure k s.K := sorry

/-- The specified closure embedding, restricted to the relative algebraic closure. -/
noncomputable def specGeometricPointAlgebraicInclusion {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    AlgebraicClosure k →ₐ[k] algebraicClosure k s.K :=
  (specGeometricPointLift s).codRestrict (algebraicClosure k s.K).toSubalgebra
    (specGeometricPointLift_mem_algebraicClosure s)

/-- The specified embedding identifies the two algebraic closures by the algebraic
Schroeder--Bernstein theorem. -/
noncomputable def specGeometricPointAlgebraicEquiv {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    AlgebraicClosure k ≃ₐ[k] algebraicClosure k s.K :=
  AlgEquiv.ofBijective (specGeometricPointAlgebraicInclusion s)
    (Algebra.IsAlgebraic.algHom_bijective₂ (specGeometricPointAlgebraicInclusion s)
      (IsAlgClosed.lift : algebraicClosure k s.K →ₐ[k] AlgebraicClosure k)).1

/-- A geometric fiber point evaluates the global functions of the finite étale cover. -/
noncomputable def specFieldPointEvaluation {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) (y : finiteEtaleFiberObj s Y) :
    Γ(Y.left, ⊤) →+* s.K :=
  (y.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of s.K)).hom).hom

/-- Values of finite étale coordinates are algebraic over the base field. -/
theorem specFieldPointEvaluation_mem_algebraicClosure {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) (y : finiteEtaleFiberObj s Y)
    (r : Γ(Y.left, ⊤)) :
    specFieldPointEvaluation s Y y r ∈ algebraicClosure k s.K := sorry

/-- Descended coordinates in the canonical algebraic closure. -/
noncomputable def specFieldDescendedEvaluation {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) (y : finiteEtaleFiberObj s Y) :
    Γ(Y.left, ⊤) →+* AlgebraicClosure k :=
  (specGeometricPointAlgebraicEquiv s).symm.toRingHom.comp
    ((specFieldPointEvaluation s Y y).codRestrict
      (algebraicClosure k s.K).toSubalgebra.toSubsemiring
      (specFieldPointEvaluation_mem_algebraicClosure s Y y))

/-- A geometric fiber point descends through its actual finite affine coordinate ring. -/
noncomputable def specPointFiberToFieldFiber {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) (y : finiteEtaleFiberObj s Y) :
    finiteEtaleFiberObj (specGaloisGeometricPoint k) Y := by
  let hfinite : AlgebraicGeometry.IsFinite Y.hom := Y.prop.1
  let haffine : IsAffineHom Y.hom := hfinite.toIsAffineHom
  let hbase : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of k))).obj Y.right) := by
    change IsAffine (Spec (CommRingCat.of k))
    infer_instance
  letI : IsAffine Y.left := @isAffine_of_isAffineHom _ _ Y.hom haffine hbase
  exact Over.homMk
    (Spec.map (CommRingCat.ofHom (specFieldDescendedEvaluation s Y y)) ≫ Y.left.isoSpec.inv)
    (w := sorry)

/-- The geometric-fiber comparison uses the specified embedding and coordinate descent. -/
noncomputable def specFieldFiberEquiv {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    finiteEtaleFiberObj (specGaloisGeometricPoint k) Y ≃ finiteEtaleFiberObj s Y :=
  { toFun := specFieldFiberToPointFiber s Y
    invFun := specPointFiberToFieldFiber s Y
    left_inv := sorry
    right_inv := sorry }

/-- The fiber comparison acts by the specified algebraic-closure embedding. -/
@[simp]
theorem specFieldFiberEquiv_apply {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k)))
    (y : finiteEtaleFiberObj (specGaloisGeometricPoint k) Y) :
    specFieldFiberEquiv s Y y = specFieldFiberToPointFiber s Y y := rfl

/-- The inverse fiber comparison acts by descent of affine coordinates. -/
@[simp]
theorem specFieldFiberEquiv_symm_apply {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) (y : finiteEtaleFiberObj s Y) :
    (specFieldFiberEquiv s Y).symm y = specPointFiberToFieldFiber s Y y := rfl

/-- Isomorphism of standard fiber functors at two geometric points of `Spec k`. -/
noncomputable def specGeometricPointFiberIso {k : Type u} [Field k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    standardFiniteEtaleFiber (specGaloisGeometricPoint k) ≅ standardFiniteEtaleFiber s :=
  NatIso.ofComponents
    (fun Y ↦
      { hom := FintypeCat.homMk (specFieldFiberEquiv s Y)
        inv := FintypeCat.homMk (specFieldFiberEquiv s Y).symm
        hom_inv_id := sorry
        inv_hom_id := sorry })
    fun _ ↦ sorry

/-- The spectrum map of a finite field extension is finite. -/
theorem specFieldExtension_finite {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] :
    AlgebraicGeometry.IsFinite
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := sorry

/-- The spectrum map of a finite separable field extension is étale. -/
theorem specFieldExtension_etale {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap k L))) := sorry

/-- The finite étale cover attached to the specified finite separable field. -/
noncomputable def specFieldExtensionCover (k L : Type u) [Field k] [Field L]
    [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    FiniteEtale (Spec (CommRingCat.of k)) :=
  { toComma := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    prop := ⟨specFieldExtension_finite, specFieldExtension_etale⟩ }

/-- The geometric point of a field cover is its specified embedding. -/
noncomputable def specFieldExtensionPoint {k L : Type u} [Field k] [Field L]
    [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (e : L →ₐ[k] AlgebraicClosure k) :
    finiteEtaleFiberObj (specGaloisGeometricPoint k) (specFieldExtensionCover k L) :=
  Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) (w := sorry)

/-- Evaluate a fiber automorphism on a specified finite separable field embedding. -/
noncomputable def specFieldExtensionActedEvaluation {k L : Type u} [Field k] [Field L]
    [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (σ : Aut (specGaloisGeometricPoint k).finiteFiber)
    (e : L →ₐ[k] AlgebraicClosure k) : L →+* AlgebraicClosure k :=
  (Spec.homEquiv
    (σ.hom.app (specFieldExtensionCover k L) (specFieldExtensionPoint e)).left).hom

/-- A fiber automorphism acts on an algebraic element through the finite field it generates. -/
noncomputable def specFiberAutApply {k : Type u} [Field k] [Fintype k]
    (σ : Aut (specGaloisGeometricPoint k).finiteFiber) (x : AlgebraicClosure k) :
    AlgebraicClosure k := by
  letI : FiniteDimensional k (IntermediateField.adjoin k {x}) :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral
  exact specFieldExtensionActedEvaluation σ (IntermediateField.adjoin k {x}).val
    ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩

/-- The algebraic-closure automorphism reconstructed by its finite-field coordinates. -/
noncomputable def specFiberAutToGalois {k : Type u} [Field k] [Fintype k]
    (σ : Aut (specGaloisGeometricPoint k).finiteFiber) : Gal(AlgebraicClosure k/k) where
  toFun := specFiberAutApply σ
  invFun := specFiberAutApply σ⁻¹
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Reconstruction acts on each algebraic element by its finite-field coordinate. -/
@[simp]
theorem specFiberAutToGalois_apply {k : Type u} [Field k] [Fintype k]
    (σ : Aut (specGaloisGeometricPoint k).finiteFiber) (x : AlgebraicClosure k) :
    specFiberAutToGalois σ x = specFiberAutApply σ x := rfl

/-- The inverse reconstructed field automorphism uses the inverse fiber automorphism. -/
@[simp]
theorem specFiberAutToGalois_symm_apply {k : Type u} [Field k] [Fintype k]
    (σ : Aut (specGaloisGeometricPoint k).finiteFiber) (x : AlgebraicClosure k) :
    (specFiberAutToGalois σ).symm x = specFiberAutApply σ⁻¹ x := rfl

/-- The image of arithmetic Frobenius in `π₁(Spec k)` at the canonical algebraic-closure
geometric point. -/
noncomputable def arithmeticFrobeniusπ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k) :=
  galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) (FiniteField.arithmeticFrobenius k)

/-- Arithmetic Frobenius transported to a general geometric point of `Spec k`. -/
noncomputable def arithmeticFrobeniusπAt {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) s :=
  inducedAutHom_of_fiberIso (specGeometricPointFiberIso s) (arithmeticFrobeniusπ (k := k))

/-- `arithmeticFrobeniusπ` is the image of `FiniteField.arithmeticFrobenius k`. -/
theorem arithmeticFrobeniusπ_spec {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    arithmeticFrobeniusπ (k := k) =
      galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) (FiniteField.arithmeticFrobenius k) :=
  sorry

/-- Geometric Frobenius in `π₁(Spec k)` at the canonical algebraic-closure geometric
point: the inverse of arithmetic Frobenius, equivalently the image of
`(FiniteField.arithmeticFrobenius k)⁻¹`. -/
noncomputable def geometricFrobeniusπ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k) :=
  (arithmeticFrobeniusπ (k := k))⁻¹

/-- Geometric Frobenius transported to a general geometric point of `Spec k`. -/
noncomputable def geometricFrobeniusπAt {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) s :=
  inducedAutHom_of_fiberIso (specGeometricPointFiberIso s) (geometricFrobeniusπ (k := k))

/-- `geometricFrobeniusπ` is the image of `(FiniteField.arithmeticFrobenius k)⁻¹`. -/
theorem geometricFrobeniusπ_spec {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    geometricFrobeniusπ (k := k) =
      galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)
        (FiniteField.arithmeticFrobenius k)⁻¹ :=
  sorry

/-- `geometricFrobeniusπ` is the inverse of `arithmeticFrobeniusπ`. -/
theorem geometricFrobeniusπ_eq_inv {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    geometricFrobeniusπ (k := k) = (arithmeticFrobeniusπ (k := k))⁻¹ :=
  sorry

/-- A finite quotient coordinate of the degree map. -/
abbrev SpecDegreeQuotient (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :=
  integerGroup.{u + 1} ⧸ H.toSubgroup

/-- The testing field has the degree of the actual finite quotient. -/
noncomputable abbrev specDegreeField (k : Type u) [Field k] [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) : Type u :=
  ULift.{u} (FiniteField.Extension k p H.toSubgroup.index)

/-- The finite-field spectrum used to read one residue of the degree map. -/
noncomputable def specDegreeCover (k : Type u) [Field k] [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    FiniteEtale (Spec (CommRingCat.of k)) := by
  letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
  exact specFieldExtensionCover k (specDegreeField k p H)

/-- A canonical library field embedding supplies the test point. -/
noncomputable def specDegreePoint (k : Type u) [Field k] [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    finiteEtaleFiberObj (specGaloisGeometricPoint k) (specDegreeCover k p H) := by
  letI : NeZero H.toSubgroup.index := ⟨H.toSubgroup.index_ne_zero_of_finite⟩
  exact specFieldExtensionPoint (IsAlgClosed.lift : specDegreeField k p H →ₐ[k] AlgebraicClosure k)

/-- Read the geometric Frobenius exponent by evaluating the finite orbit of a test point. -/
noncomputable def specDegreeCoordinate {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1})
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k)) :
    SpecDegreeQuotient H := by
  classical
  exact ∏ j : Fin H.toSubgroup.index,
    if σ.hom.app (specDegreeCover k p H) (specDegreePoint k p H) =
        (geometricFrobeniusπ (k := k) ^ j.val).hom.app
          (specDegreeCover k p H) (specDegreePoint k p H)
    then QuotientGroup.mk (Multiplicative.ofAdd (ULift.up (j.val : ℤ)))
    else 1

/-- Naturality of fiber automorphisms makes the finite quotient coordinates compatible. -/
theorem specDegreeCoordinate_naturality {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    {H L : FiniteIndexNormalSubgroup integerGroup.{u + 1}} (f : H ⟶ L)
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k)) :
    (ProfiniteCompletion.diagram integerGroup).map f (specDegreeCoordinate H σ) =
      specDegreeCoordinate L σ := sorry

/-- The degree is the actual compatible tuple of finite-field evaluations. -/
noncomputable def specDegreeTuple {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k)) :
    hatZ.{u + 1} :=
  ⟨fun H ↦ specDegreeCoordinate H σ, fun _ _ f ↦ specDegreeCoordinate_naturality f σ⟩

/-- The residue of the degree tuple is its specified finite-field computation. -/
@[simp]
theorem specDegreeTuple_apply {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k))
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    (specDegreeTuple σ).val H = specDegreeCoordinate H σ := rfl


/-- Existence and uniqueness of the continuous surjection `π₁(Spec k) ⟶ hatZ` sending
geometric Frobenius to `1`. -/
theorem existsUnique_specToHatZ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    ∃! f : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k) ⟶
        hatZ.{u + 1},
      Function.Surjective f ∧ f (geometricFrobeniusπ (k := k)) = hatZOne.{u + 1} :=
  sorry

/-- The unique continuous surjection `π₁(Spec k) ⟶ hatZ` sending geometric Frobenius to
the generator `1`. -/
noncomputable def specToHatZ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k) ⟶
      hatZ.{u + 1} :=
  ProfiniteGrp.ofHom
    { toFun := specDegreeTuple
      map_one' := sorry
      map_mul' := sorry
      continuous_toFun := sorry }

/-- Each finite quotient coordinate of the degree map is its finite-orbit evaluation. -/
@[simp]
theorem specToHatZ_apply {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k))
    (H : FiniteIndexNormalSubgroup integerGroup.{u + 1}) :
    (specToHatZ (k := k) σ).val H = specDegreeCoordinate H σ := rfl

/-- The degree map at a general geometric point, obtained by transporting `specToHatZ`
along the fiber identification. -/
noncomputable def specToHatZAt {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) s ⟶ hatZ.{u + 1} :=
  ProfiniteGrp.ofHom (inducedAutHom_of_fiberIso (specGeometricPointFiberIso s).symm) ≫
    specToHatZ (k := k)

/-- The degree map `π₁(Spec k) ⟶ hatZ` is surjective. -/
theorem specToHatZ_surjective {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    Function.Surjective (specToHatZ (k := k)) :=
  sorry

/-- `specToHatZ` sends geometric Frobenius to the generator `1` of `hatZ`. -/
theorem specToHatZ_geometricFrobenius {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    specToHatZ (k := k) (geometricFrobeniusπ (k := k)) = hatZOne.{u + 1} :=
  sorry

/-- `specToHatZAt` sends the transported geometric Frobenius to `1`. -/
theorem specToHatZAt_geometricFrobenius {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    specToHatZAt s (geometricFrobeniusπAt s) = hatZOne.{u + 1} :=
  sorry

/-- A continuous surjection `π₁(Spec k) ⟶ hatZ` sending geometric Frobenius to `1`
equals `specToHatZ`. -/
theorem specToHatZ_unique {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (f : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k) ⟶
      hatZ.{u + 1})
    (hf : Function.Surjective f)
    (hF : f (geometricFrobeniusπ (k := k)) = hatZOne.{u + 1}) :
    f = specToHatZ (k := k) :=
  sorry

/-- Geometric connectedness makes the arithmetic projection, and hence the normalized
finite-field degree map, surjective. -/
theorem geometricDegree_surjective {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) :
    Function.Surjective
      (arithmeticToGalois X etaBar ≫ specToHatZAt (galoisPoint X etaBar)) := sorry

/-- The étale fundamental group of a geometrically connected scheme over a finite
field, as a degree extension of `hatZ`. The degree map is `arithmeticToGalois`
followed by the unique geometric-Frobenius-normalized map `specToHatZAt`. -/
noncomputable def ofEtaleFundamentalGroup {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) : DegreeExtension.{u + 1} where
  middle := etaleFundamentalGroup X.left etaBar
  deg := arithmeticToGalois X etaBar ≫ specToHatZAt (galoisPoint X etaBar)
  deg_surjective := geometricDegree_surjective X etaBar

/-- Unfolding of `ofEtaleFundamentalGroup` on the middle group. -/
theorem ofEtaleFundamentalGroup_middle {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) :
    (ofEtaleFundamentalGroup X etaBar).middle = etaleFundamentalGroup X.left etaBar :=
  sorry

/-- Unfolding of `ofEtaleFundamentalGroup.deg` as `arithmeticToGalois` followed by
`specToHatZAt`. -/
theorem ofEtaleFundamentalGroup_deg {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) :
    (ofEtaleFundamentalGroup X etaBar).deg =
      arithmeticToGalois X etaBar ≫ specToHatZAt (galoisPoint X etaBar) :=
  sorry

/-- The identification of `Gal(k̄/k)` with `π₁(Spec k)` at the canonical algebraic-closure
point, sending arithmetic Frobenius to `arithmeticFrobeniusπ`. -/
noncomputable def galoisEquivEtaleFundamentalGroup {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))] :
    Gal(AlgebraicClosure k/k) ≃*
      etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k) :=
  { toFun := galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)
    invFun := specFiberAutToGalois
    left_inv := sorry
    right_inv := sorry
    map_mul' := (galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)).map_mul }

/-- The reverse Galois comparison is evaluation on finite generated subfields. -/
@[simp]
theorem galoisEquivEtaleFundamentalGroup_symm_apply {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (σ : etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k)) :
    (galoisEquivEtaleFundamentalGroup (k := k)).symm σ = specFiberAutToGalois σ := rfl

/-- The homomorphism `G = ker(deg) → Gal(k̄/k)` obtained from the arithmetic-to-Galois
sequence of `ofEtaleFundamentalGroup`. -/
noncomputable def galoisFromKer {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) :
    (ofEtaleFundamentalGroup X etaBar).G →* Gal(AlgebraicClosure k/k) :=
  (galoisEquivEtaleFundamentalGroup (k := k)).symm.toMonoidHom.comp
    ((inducedAutHom_of_fiberIso
        (specGeometricPointFiberIso (galoisPoint X etaBar)).symm).toMonoidHom.comp
      ((arithmeticToGalois X etaBar).hom.toMonoidHom.comp
        (ofEtaleFundamentalGroup X etaBar).inlHom))

/-- Unfolding of `galoisFromKer` as the composite through `arithmeticToGalois`. -/
theorem galoisFromKer_spec {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) :
    galoisFromKer X etaBar =
      (galoisEquivEtaleFundamentalGroup (k := k)).symm.toMonoidHom.comp
        ((inducedAutHom_of_fiberIso
            (specGeometricPointFiberIso (galoisPoint X etaBar)).symm).toMonoidHom.comp
          ((arithmeticToGalois X etaBar).hom.toMonoidHom.comp
            (ofEtaleFundamentalGroup X etaBar).inlHom)) :=
  sorry

end ProfiniteGrp.DegreeExtension
