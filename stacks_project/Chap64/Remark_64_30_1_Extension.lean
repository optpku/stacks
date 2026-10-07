module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.ULift
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap58.Lemma_58_6_3_GaloisFiber
public import stacks_project.Chap58.Remark_58_6_4_GaloisAction
public import stacks_project.Chap58.Theorem_58_6_2_Fiber
public import stacks_project.Chap58.Theorem_58_6_2_InducedHom
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»

/-!
# Profinite degree extensions of `hatZ`

This leaf owns the profinite integers `hatZ`, short exact sequences
`1 → G → Γ → hatZ → 1`, conjugacy-class degree, and the étale fundamental-group
example, with degree map `arithmeticToGalois` followed by the geometric
Frobenius-normalized isomorphism `π₁(Spec k) ⟶ hatZ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.SchemeOverField
open scoped Topology

universe u

namespace ProfiniteGrp

/-- The profinite completion of the infinite cyclic group. -/
noncomputable abbrev hatZ : ProfiniteGrp.{u} :=
  ProfiniteCompletion.completion (GrpCat.of (Multiplicative (ULift.{u} ℤ)))

/-- The canonical image of `n : ℕ` in `hatZ`. -/
noncomputable def hatZNatCast (n : ℕ) : hatZ.{u} :=
  ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative (ULift.{u} ℤ)))
    (Multiplicative.ofAdd (ULift.up (n : ℤ)))

/-- The canonical generator `1` in `hatZ`. -/
noncomputable def hatZOne : hatZ.{u} :=
  hatZNatCast 1

/-- A profinite extension `1 → G → Γ →deg hatZ → 1`, with `G` recovered as `ker(deg)`. -/
structure DegreeExtension where
  /-- The middle profinite group of the extension. -/
  middle : ProfiniteGrp.{u}
  /-- The degree homomorphism `Γ ⟶ hatZ`. -/
  deg : middle ⟶ hatZ.{u}
  /-- The degree homomorphism is surjective. -/
  deg_surjective : Function.Surjective deg

namespace DegreeExtension

variable (S : DegreeExtension.{u})

/-- The kernel of `deg` as a closed subgroup of `Γ`. -/
noncomputable def kerClosed : ClosedSubgroup S.middle where
  toSubgroup := MonoidHom.ker S.deg.hom.toMonoidHom
  isClosed' := IsClosed.preimage S.deg.hom.continuous
      (isClosed_singleton : IsClosed ({1} : Set hatZ.{u}))

/-- The kernel `G = ker(deg)`, as a topological group. -/
abbrev G : Type u := S.kerClosed.toSubgroup

/-- The inclusion homomorphism `G →* Γ`. -/
noncomputable def inlHom : S.G →* S.middle :=
  S.kerClosed.subtype

/-- The inclusion `G →ₜ* Γ` of the kernel of `deg`. -/
noncomputable def inl : S.G →ₜ* S.middle :=
  ⟨S.kerClosed.subtype, sorry⟩

/-- The degree of a conjugacy class, well-defined because `hatZ` is abelian. -/
noncomputable def degClass (c : ConjClasses S.middle) : hatZ.{u} :=
  S.deg (Quotient.out c)

/-- A chosen degree-one lift of `1` in `hatZ`. -/
noncomputable def degreeOneLift : S.middle :=
  Classical.choose (S.deg_surjective hatZOne)

/-- The chosen degree-one lift maps to `1` in `hatZ`. -/
theorem deg_degreeOneLift : S.deg S.degreeOneLift = hatZOne.{u} :=
  sorry

/-- Any two degree-one lifts differ by an element of `G = ker(deg)`. -/
theorem degreeOneLift_spec (γ : S.middle) :
    S.deg γ = hatZOne.{u} ↔ ∃ g : S.G, γ = S.inl g * S.degreeOneLift :=
  sorry

/-- The conjugacy class of a chosen degree-one lift, recording `F = 1` in `Γ/G = hatZ`. -/
noncomputable def frobenius : ConjClasses S.middle :=
  ConjClasses.mk S.degreeOneLift

/-- Conjugation by `γ` on the kernel of `deg`. -/
noncomputable def conjHom (γ : S.middle) : S.G →ₜ* S.G :=
  ⟨{ toFun := fun g => ⟨γ * g.val * γ⁻¹, sorry⟩
     map_one' := sorry
     map_mul' := sorry },
    sorry⟩

/-- Package a surjective degree map as a degree extension. -/
noncomputable def ofSurjectiveDeg (middle : ProfiniteGrp.{u}) (deg : middle ⟶ hatZ.{u})
    (h : Function.Surjective deg) : DegreeExtension.{u} where
  middle := middle
  deg := deg
  deg_surjective := h

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

/-- Equivalence of finite étale fibers at the canonical algebraic-closure point and at
a general geometric point of `Spec k`. -/
noncomputable def specFieldFiberEquiv {k : Type u} [Field k]
    (s : GeometricPoint (Spec (CommRingCat.of k)))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    finiteEtaleFiberObj (specGaloisGeometricPoint k) Y ≃ finiteEtaleFiberObj s Y :=
  Equiv.ofBijective (specFieldFiberToPointFiber s Y)
    (specFieldFiberToPointFiber_bijective s Y)

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

/-- The image of arithmetic Frobenius in `π₁(Spec k)` at the canonical algebraic-closure
geometric point. -/
noncomputable def arithmeticFrobeniusπ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) (specGaloisGeometricPoint k) :=
  galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) arithmeticFrobeniusEquiv

/-- Arithmetic Frobenius transported to a general geometric point of `Spec k`. -/
noncomputable def arithmeticFrobeniusπAt {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (s : GeometricPoint (Spec (CommRingCat.of k))) :
    etaleFundamentalGroup (Spec (CommRingCat.of k)) s :=
  inducedAutHom_of_fiberIso (specGeometricPointFiberIso s) (arithmeticFrobeniusπ (k := k))

/-- `arithmeticFrobeniusπ` is the image of `arithmeticFrobeniusEquiv`. -/
theorem arithmeticFrobeniusπ_spec {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    arithmeticFrobeniusπ (k := k) =
      galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k) arithmeticFrobeniusEquiv :=
  sorry

/-- Geometric Frobenius in `π₁(Spec k)` at the canonical algebraic-closure geometric
point: the inverse of arithmetic Frobenius, equivalently the image of
`arithmeticFrobeniusEquiv⁻¹`. -/
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

/-- `geometricFrobeniusπ` is the image of `arithmeticFrobeniusEquiv⁻¹`. -/
theorem geometricFrobeniusπ_spec {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    geometricFrobeniusπ (k := k) =
      galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)
        (arithmeticFrobeniusEquiv (k := k))⁻¹ :=
  sorry

/-- `geometricFrobeniusπ` is the inverse of `arithmeticFrobeniusπ`. -/
theorem geometricFrobeniusπ_eq_inv {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] :
    geometricFrobeniusπ (k := k) = (arithmeticFrobeniusπ (k := k))⁻¹ :=
  sorry

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
  Classical.choose (ExistsUnique.exists (existsUnique_specToHatZ (k := k)))

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

/-- The étale fundamental group of a geometrically connected scheme over a finite
field, as a degree extension of `hatZ`. The degree map is `arithmeticToGalois`
followed by the unique geometric-Frobenius-normalized map `specToHatZAt`. -/
noncomputable def ofEtaleFundamentalGroup {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) : DegreeExtension.{u + 1} where
  middle := etaleFundamentalGroup X.left etaBar
  deg := arithmeticToGalois X etaBar ≫ specToHatZAt (galoisPoint X etaBar)
  deg_surjective := sorry

/-- Unfolding of `ofEtaleFundamentalGroup` on the middle group. -/
theorem ofEtaleFundamentalGroup_middle {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) :
    (ofEtaleFundamentalGroup X etaBar).middle = etaleFundamentalGroup X.left etaBar :=
  sorry

/-- Unfolding of `ofEtaleFundamentalGroup.deg` as `arithmeticToGalois` followed by
`specToHatZAt`. -/
theorem ofEtaleFundamentalGroup_deg {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
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
  MulEquiv.ofBijective (galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k)) sorry

/-- The homomorphism `G = ker(deg) → Gal(k̄/k)` obtained from the arithmetic-to-Galois
sequence of `ofEtaleFundamentalGroup`. -/
noncomputable def galoisFromKer {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (X : SchemeOverField k) [ConnectedSpace X.left]
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
    [ConnectedSpace (Spec (CommRingCat.of k))]
    (etaBar : GeometricPoint X.left) :
    galoisFromKer X etaBar =
      (galoisEquivEtaleFundamentalGroup (k := k)).symm.toMonoidHom.comp
        ((inducedAutHom_of_fiberIso
            (specGeometricPointFiberIso (galoisPoint X etaBar)).symm).toMonoidHom.comp
          ((arithmeticToGalois X etaBar).hom.toMonoidHom.comp
            (ofEtaleFundamentalGroup X etaBar).inlHom)) :=
  sorry

end DegreeExtension

end ProfiniteGrp
