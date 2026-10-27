/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.PullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Section

/-!
# Projective schemes of vector spaces

For a vector space `V` over a field `k`, this file constructs the projective scheme
`Proj(SymmetricAlgebra k V)`, its structure morphism, its comparison with standard projective
space after choosing a basis, and its functorial description by invertible quotients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The module sheaf on `Spec(k)` associated to a `k`-vector space. -/
noncomputable abbrev moduleSheaf
    (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] :
    (Spec (CommRingCat.of k)).Modules :=
  (tilde (ModuleCat.of (CommRingCat.of k) V) :
    (Spec (CommRingCat.of k)).Modules)

/-- The global section of the affine module sheaf associated to a vector. -/
noncomputable abbrev moduleSection (v : V) : (moduleSheaf k V).sections :=
  RingedSpace.sectionFromTop (moduleSheaf k V)
    ((tilde.isoTop (ModuleCat.of (CommRingCat.of k) V)).hom v)

/-- The section associated to a vector is obtained through the affine tilde comparison. -/
theorem moduleSection_def (v : V) :
    moduleSection v =
      RingedSpace.sectionFromTop (moduleSheaf k V)
        ((tilde.isoTop (ModuleCat.of (CommRingCat.of k) V)).hom v) :=
  rfl

/-- The grading of the symmetric algebra by powers of its degree-one image. -/
abbrev grading
    (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] :
    ℕ → Submodule k (SymmetricAlgebra k V) :=
  (LinearMap.range (SymmetricAlgebra.ι k V : V →ₗ[k] SymmetricAlgebra k V) ^ ·)

/-- The degree-one generator map for the direct-sum decomposition of the symmetric algebra. -/
noncomputable def gradedAlgebraGenerator :
    V →ₗ[k] DirectSum ℕ (fun i ↦ ↥(grading k V i)) :=
  DirectSum.lof k ℕ (fun i ↦ ↥(grading k V i)) 1 ∘ₗ
    (SymmetricAlgebra.ι k V).codRestrict _ fun v ↦ by
      simpa [grading] using LinearMap.mem_range_self (SymmetricAlgebra.ι k V) v

/-- The explicit homogeneous decomposition map for the symmetric algebra. -/
noncomputable def gradedAlgebraDecompose :
    SymmetricAlgebra k V →ₐ[k] DirectSum ℕ (fun i ↦ ↥(grading k V i)) :=
  SymmetricAlgebra.lift gradedAlgebraGenerator

/-- Recombining the homogeneous decomposition of the symmetric algebra is the identity. -/
theorem gradedAlgebra_rightInv :
    (DirectSum.coeAlgHom (grading k V)).comp gradedAlgebraDecompose =
      AlgHom.id k (SymmetricAlgebra k V) := sorry

/-- A homogeneous element decomposes into its given direct-sum component. -/
theorem gradedAlgebra_leftInv (i : ℕ) (x : grading k V i) :
    gradedAlgebraDecompose (x : SymmetricAlgebra k V) =
      DirectSum.of (fun j ↦ ↥(grading k V j)) i x := sorry

/-- The powers-of-degree-one grading is the canonical graded algebra structure on the symmetric
algebra. -/
noncomputable instance grading_gradedAlgebra :
    GradedAlgebra (grading k V) :=
  GradedAlgebra.ofAlgHom (grading k V) gradedAlgebraDecompose
    gradedAlgebra_rightInv gradedAlgebra_leftInv

/-- Scalar constants lie in degree zero of the symmetric algebra. -/
theorem degreeZero_mem (r : k) :
    algebraMap k (SymmetricAlgebra k V) r ∈ grading k V 0 := sorry

/-- The inverse-to-algebra-map formula holds on the degree-zero component. -/
theorem degreeZero_leftInv (x : grading k V 0) :
    algebraMap k (SymmetricAlgebra k V)
        (SymmetricAlgebra.algebraMapInv x.1) = x.1 := sorry

/-- The inverse-to-algebra-map formula preserves multiplication on degree zero. -/
theorem degreeZero_map_mul (x y : grading k V 0) :
    SymmetricAlgebra.algebraMapInv (x * y).1 =
      SymmetricAlgebra.algebraMapInv x.1 *
        SymmetricAlgebra.algebraMapInv y.1 := sorry

/-- The inverse-to-algebra-map formula preserves addition on degree zero. -/
theorem degreeZero_map_add (x y : grading k V 0) :
    SymmetricAlgebra.algebraMapInv (x + y).1 =
      SymmetricAlgebra.algebraMapInv x.1 +
        SymmetricAlgebra.algebraMapInv y.1 := sorry

/-- The degree-zero component of the symmetric algebra is canonically the base field. -/
noncomputable def degreeZeroRingEquiv
    (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] :
    grading k V 0 ≃+* k where
  toFun x := SymmetricAlgebra.algebraMapInv x.1
  invFun r := ⟨algebraMap k (SymmetricAlgebra k V) r, degreeZero_mem r⟩
  left_inv x := Subtype.ext (degreeZero_leftInv x)
  right_inv := SymmetricAlgebra.algebraMap_leftInverse V
  map_mul' := degreeZero_map_mul
  map_add' := degreeZero_map_add

/-- The projective scheme of `V` is the projective spectrum of its symmetric algebra. -/
noncomputable abbrev scheme
    (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] :
    Scheme.{u} :=
  Proj (grading k V)

/-- The canonical structure morphism from the projective scheme of a vector space to its affine
base. -/
noncomputable def toSpec
    (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V] :
    scheme k V ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (grading k V) ≫
    (Scheme.Spec.mapIso (degreeZeroRingEquiv k V).toCommRingCatIso.op).symm.hom

/-- The basis-induced algebra equivalence preserves each homogeneous component. -/
theorem basisComparison_map_mem
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V) {d : ℕ}
    {x : MvPolynomial (Fin (n + 1)) k}
    (hx : x ∈ ProjectiveSpace.grading k n d) :
    (SymmetricAlgebra.equivMvPolynomial b).symm x ∈ grading k V d := sorry

/-- The basis-induced graded map satisfies the irrelevant-ideal condition for a projective
spectrum morphism. -/
theorem basisComparison_irrelevant
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V) :
    HomogeneousIdeal.irrelevant (grading k V) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveSpace.grading k n)).map
        { toRingHom := (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom
          map_mem := basisComparison_map_mem n b } := sorry

/-- A basis identifies the projective scheme of a vector space with standard projective space
through the induced projective-spectrum morphism. -/
noncomputable def basisComparison
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V) :
    scheme k V ⟶ ProjectiveSpace.scheme k n :=
  let f : ProjectiveSpace.grading k n →+*ᵍ grading k V :=
    { toRingHom := (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom
      map_mem := basisComparison_map_mem n b }
  Proj.map f (basisComparison_irrelevant n b)

/-- The projective-spectrum comparison associated to a basis is an isomorphism. -/
theorem basisComparison_isIso
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V) :
    IsIso (basisComparison n b) := sorry

/-- The basis comparison commutes with the structure morphisms to `Spec(k)`. -/
theorem basisComparison_toSpec
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V) :
    basisComparison n b ≫ ProjectiveSpace.toSpec k n = toSpec k V := sorry

/-- A finite-dimensional vector space of dimension `n + 1` has projective scheme isomorphic
to standard projective `n`-space. -/
theorem nonemptyIsoProjectiveSpaceOfFinrankEq
    [FiniteDimensional k V] (n : ℕ) (hV : Module.finrank k V = n + 1) :
    Nonempty (scheme k V ≅ ProjectiveSpace.scheme k n) := sorry

/-- A projective-bundle model of the symmetric projective spectrum exists. This proposition is
not used to select canonical morphisms or comparison maps; these are constructed directly from
the fixed symmetric coordinates. -/
theorem hasProjectiveBundleRepresentation :
    Nonempty (Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V)) := sorry

/-- The tautological invertible module of a chosen quotient representation of the projective
scheme. -/
noncomputable abbrev tautologicalSheaf
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V)) :
    (scheme k V).Modules :=
  Scheme.ProjectiveBundle.tautologicalSheaf (toSpec k V) hP

/-- The specialized tautological module unfolds to the projective-bundle tautological module. -/
theorem tautologicalSheaf_def
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V)) :
    tautologicalSheaf hP =
      Scheme.ProjectiveBundle.tautologicalSheaf (toSpec k V) hP :=
  rfl

/-- The fixed Serre sheaf O(1) on the symmetric-algebra projective spectrum. Unlike a supplied
model's tautological target, this object is fixed by the symmetric coordinates. -/
noncomputable abbrev canonicalTautologicalSheaf : (scheme k V).Modules :=
  Proj.AssociatedModule.twistingSheaf (grading k V) 1

/-- The actual homogeneous fraction v/1 defining the canonical degree-one section. -/
noncomputable def tautologicalSection (v : V) : Γ(canonicalTautologicalSheaf (k := k) (V := V), ⊤) :=
  Proj.AssociatedModule.degreeZeroToGlobalSections (grading k V)
    (GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading (grading k V)) 1)
    ⟨SymmetricAlgebra.ι k V v, by
      simpa [grading] using LinearMap.mem_range_self (SymmetricAlgebra.ι k V) v⟩

/-- The degree-one standard open defined by v. -/
def vectorBasicOpen (v : V) : (scheme k V).Opens :=
  Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v)

/-- The canonical k-linear degree-one section map, with v sent to the actual fraction v/1. -/
noncomputable def tautologicalLinearMap : ModuleCat.of k V ⟶
    Scheme.Hom.globalSectionsMod (toSpec k V)
      (canonicalTautologicalSheaf (k := k) (V := V)) :=
  @ModuleCat.ofHom k _ V
    (Scheme.Hom.globalSectionsMod (toSpec k V)
      (canonicalTautologicalSheaf (k := k) (V := V))) _ _ _ _
    { toFun := tautologicalSection
      map_add' := by intros; sorry
      map_smul' := by intros; sorry }

/-- The actual tautological sheaf morphism adjoint to the canonical degree-one sections. -/
noncomputable def canonicalTautologicalMap :
    (Scheme.Modules.pullback (toSpec k V)).obj (moduleSheaf k V) ⟶
      canonicalTautologicalSheaf (k := k) (V := V) :=
  Scheme.Modules.pullbackTildeHom (toSpec k V) (ModuleCat.of k V)
    (canonicalTautologicalSheaf (k := k) (V := V)) tautologicalLinearMap

/-- The actual degree-one Serre sheaf on a symmetric projective spectrum is invertible. -/
theorem canonicalTautologicalSheaf_isInvertible :
    Scheme.Modules.Invertible (canonicalTautologicalSheaf (k := k) (V := V)) := sorry

/-- The actual degree-one generators give an epimorphic tautological map. -/
theorem canonicalTautologicalMap_epi :
    Epi (canonicalTautologicalMap (k := k) (V := V)) := sorry

/-- The canonical tautological quotient has its actual Serre target and actual section-adjoint
morphism. Its invertibility and epimorphy fields are propositions. -/
noncomputable def canonicalTautologicalQuotient :
    CategoryTheory.InvertibleQuotient
      ((Scheme.Modules.pullback (toSpec k V)).obj (moduleSheaf k V)) where
  object := canonicalTautologicalSheaf (k := k) (V := V)
  isInvertible := canonicalTautologicalSheaf_isInvertible
  hom := canonicalTautologicalMap
  hom_epi := canonicalTautologicalMap_epi

/-- Explicit compatibility of a supplied projective-bundle model with the fixed symmetric
coordinates. This data is required whenever such a model is compared with the canonical map. -/
structure CanonicalCoordinates
    (hP : Scheme.ProjectiveBundle.Representation (toSpec k V) (moduleSheaf k V)) where
  /-- The supplied target is explicitly identified with the actual Serre sheaf O(1). -/
  targetIso : tautologicalSheaf hP ≅ canonicalTautologicalSheaf (k := k) (V := V)
  /-- The target identification carries the supplied tautological map to the actual v/1 map. -/
  quotient_commutes : (Scheme.ProjectiveBundle.tautologicalQuotient (toSpec k V) hP).hom ≫
    targetIso.hom = canonicalTautologicalMap

/-- Divide a degree-one localized fraction by a vector that is invertible at the point.
The only choices unpack the homogeneous representative already stored in `z.property`;
they do not select a map or inverse from an existence theorem. -/
noncomputable def tautologicalRatioAtPoint (v : V) (x : scheme k V)
    (hx : x ∈ vectorBasicOpen v)
    (z : Proj.AssociatedModule.atPoint (grading k V)
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading (grading k V)) 1) x) :
    HomogeneousLocalization.AtPrime (grading k V) x.asHomogeneousIdeal.toIdeal :=
  let n := Classical.choose z.property
  let m := Classical.choose (Classical.choose_spec z.property)
  let d := Classical.choose (Classical.choose_spec (Classical.choose_spec z.property))
  let hd := Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec z.property)))
  HomogeneousLocalization.mk
    { deg := n + 1
      num := ⟨(m : SymmetricAlgebra k V), by sorry⟩
      den := ⟨(d : SymmetricAlgebra k V) * SymmetricAlgebra.ι k V v, by sorry⟩
      den_mem := x.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hd hx }

/-- The quotient-representative-independent meaning of the local ratio: m/d is sent to m/(dv).
Its value in the ordinary localization is multiplication by 1/v. -/
theorem tautologicalRatioAtPoint_val (v : V) (x : scheme k V)
    (hx : x ∈ vectorBasicOpen v)
    (z : Proj.AssociatedModule.atPoint (grading k V)
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading (grading k V)) 1) x) :
    (tautologicalRatioAtPoint v x hx z).val =
      (z : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl (SymmetricAlgebra k V)) *
        LocalizedModule.mk 1 ⟨SymmetricAlgebra.ι k V v, hx⟩ := sorry

/-- Division by v converts actual O(1) sections on an open contained in D+(v) to regular
functions on that open. The function is defined pointwise by the homogeneous fraction formula. -/
noncomputable def tautologicalRatio (v : V) (U : (scheme k V).Opens)
    (hU : U ≤ vectorBasicOpen v)
    (s : (canonicalTautologicalSheaf (k := k) (V := V)).val.obj (Opposite.op U)) :
    Γ(scheme k V, U) :=
  ⟨fun x ↦ tautologicalRatioAtPoint v x.1 (hU x.2) (s.1 x), by sorry⟩

/-- On D+(v), the ratio of the canonical section w/1 by v is the coordinate w/v. -/
theorem tautologicalRatio_section (v w : V) (U : (scheme k V).Opens)
    (hU : U ≤ vectorBasicOpen v) (x : U) :
    (tautologicalRatio v U hU
      (((canonicalTautologicalSheaf (k := k) (V := V)).val.map
        (homOfLE (show U ≤ ⊤ from le_top)).op).hom (tautologicalSection w))).1 x =
      HomogeneousLocalization.mk
        ⟨1, ⟨SymmetricAlgebra.ι k V w, by
          simpa [grading] using LinearMap.mem_range_self (SymmetricAlgebra.ι k V) w⟩,
          ⟨SymmetricAlgebra.ι k V v, by
            simpa [grading] using LinearMap.mem_range_self (SymmetricAlgebra.ι k V) v⟩,
          hU x.2⟩ := sorry

/-- Opens contained in one of the actual degree-one standard opens. -/
def tautologicalBasis : Set ((scheme k V).Opens) :=
  {U | ∃ v : V, U ≤ vectorBasicOpen v}

/-- The symmetric algebra is generated in degree one, so the degree-one standard opens cover
and their open refinements form a basis. -/
theorem tautologicalBasis_isBasis :
    TopologicalSpace.Opens.IsBasis (tautologicalBasis (k := k) (V := V)) := sorry

/-- A quotient of the affine module sheaf determines a bundled linear map into the global
sections of its target. -/
noncomputable def quotientLinearMap
    (q : CategoryTheory.InvertibleQuotient (moduleSheaf k V)) :
    ModuleCat.of k V ⟶
      Scheme.Hom.globalSectionsMod (𝟙 (Spec (CommRingCat.of k))) q.object :=
  Scheme.Modules.pullbackTildeHomEquiv
    (𝟙 (Spec (CommRingCat.of k))) (ModuleCat.of k V) q.object
      (((Scheme.Modules.pullbackId (Spec (CommRingCat.of k))).app
        (moduleSheaf k V)).hom ≫ q.hom)

/-- The adjoint of the bundled quotient linear map is the quotient sheaf morphism, transported
along pullback by the identity. -/
theorem quotientLinearMap_apply
    (q : CategoryTheory.InvertibleQuotient (moduleSheaf k V)) :
    Scheme.Modules.pullbackTildeHom
        (𝟙 (Spec (CommRingCat.of k))) (ModuleCat.of k V) q.object
        (quotientLinearMap q) =
      ((Scheme.Modules.pullbackId (Spec (CommRingCat.of k))).app
        (moduleSheaf k V)).hom ≫ q.hom := sorry

/-- The bundled linear map associated to an invertible quotient is surjective. -/
theorem quotientLinearMap_surjective
    (q : CategoryTheory.InvertibleQuotient (moduleSheaf k V)) :
    Function.Surjective (quotientLinearMap q) := sorry

/-- The global-section vector space of the target of an invertible quotient over a field has
dimension one. -/
theorem quotientLine_finrank_eq_one
    (q : CategoryTheory.InvertibleQuotient (moduleSheaf k V)) :
    Module.finrank k
      (Scheme.Hom.globalSectionsMod (𝟙 (Spec (CommRingCat.of k))) q.object) = 1 := sorry

/-- A rational point over the base field, together with its structure-morphism equation, is a
lift of the identity through the projective scheme. -/
def pointAsLift
    (p : Spec (CommRingCat.of k) ⟶ scheme k V)
    (hp : p ≫ toSpec k V = 𝟙 (Spec (CommRingCat.of k))) :
    Scheme.ProjectiveBundle.Lift (toSpec k V)
      (𝟙 (Spec (CommRingCat.of k))) :=
  ⟨p, hp⟩

/-- Rational points expressed as lifts are equivalent to compatible quotient-isomorphism classes of the associated
affine module sheaf. -/
noncomputable def pointEquivQuotient
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V)) :
    Scheme.ProjectiveBundle.Lift (toSpec k V)
        (𝟙 (Spec (CommRingCat.of k))) ≃
      CategoryTheory.InvertibleQuotient.IsoClass (moduleSheaf k V) :=
  Scheme.ProjectiveBundle.sectionLiftEquiv (toSpec k V) hP

/-- The invertible quotient classified by a rational point. -/
noncomputable def pointQuotient
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (p : Spec (CommRingCat.of k) ⟶ scheme k V)
    (hp : p ≫ toSpec k V = 𝟙 (Spec (CommRingCat.of k))) :
    CategoryTheory.InvertibleQuotient (moduleSheaf k V) :=
  Scheme.ProjectiveBundle.sectionQuotient (toSpec k V) hP (pointAsLift p hp)

/-- The one-dimensional module sheaf classified by a rational point. -/
noncomputable def pointLineBundle
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (p : Spec (CommRingCat.of k) ⟶ scheme k V)
    (hp : p ≫ toSpec k V = 𝟙 (Spec (CommRingCat.of k))) :
    (Spec (CommRingCat.of k)).Modules :=
  (pointQuotient hP p hp).object

/-- The bundled quotient linear map classified by a rational point. -/
noncomputable def pointLinearMap
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (p : Spec (CommRingCat.of k) ⟶ scheme k V)
    (hp : p ≫ toSpec k V = 𝟙 (Spec (CommRingCat.of k))) :
    ModuleCat.of k V ⟶
      Scheme.Hom.globalSectionsMod (𝟙 (Spec (CommRingCat.of k)))
        (pointLineBundle hP p hp) :=
  quotientLinearMap (pointQuotient hP p hp)

/-- The quotient linear map classified by a rational point is surjective. -/
theorem pointLinearMap_surjective
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (p : Spec (CommRingCat.of k) ⟶ scheme k V)
    (hp : p ≫ toSpec k V = 𝟙 (Spec (CommRingCat.of k))) :
    Function.Surjective (pointLinearMap hP p hp) := sorry

/-- The target line of the quotient classified by a rational point has global-section dimension
one over the base field. -/
theorem pointLineBundle_finrank_eq_one
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (p : Spec (CommRingCat.of k) ⟶ scheme k V)
    (hp : p ≫ toSpec k V = 𝟙 (Spec (CommRingCat.of k))) :
    Module.finrank k
      (Scheme.Hom.globalSectionsMod (𝟙 (Spec (CommRingCat.of k)))
        (pointLineBundle hP p hp)) = 1 := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace
