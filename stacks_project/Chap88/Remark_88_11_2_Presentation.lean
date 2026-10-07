module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_28_1_Universal_property_restricted_power_series_RestrictedPowerSeries

/-!
# Restricted-power-series presentations and their Jacobian complexes

This leaf owns presentations `B = A{x_ι} / J` of an `A`-algebra as a quotient of a
restricted power series ring, together with the two-term Jacobian complex
`(J / J² ⟶ ⊕ᵢ B dx_i)`.
-/

@[expose] public section

open Algebra.Extension
open CategoryTheory
open RestrictedPowerSeries

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Restricted

/-- A presentation of an `A`-algebra `B` as a quotient of a restricted power
series ring `A{x_ι}`. -/
structure Presentation (A B : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B] [Algebra A B]
    (ι : Type u) where
  /-- The structure map `A{x_ι} →ₐ[A] B`. -/
  toAlgHom : RestrictedPowerSeries ι A →ₐ[A] B
  /-- The structure map is surjective. -/
  surjective : Function.Surjective toAlgHom

namespace Presentation

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing B] [Algebra A B]
variable {ι : Type u}

/-- The quotient presentation `B = A{x_ι} / J`. -/
def ofQuotient (J : Ideal (RestrictedPowerSeries ι A)) :
    Presentation A (RestrictedPowerSeries ι A ⧸ J) ι where
  toAlgHom := Ideal.Quotient.mkₐ A J
  surjective := Ideal.Quotient.mk_surjective

/-- Bundle a surjective map out of `A{x_ι}` as a restricted-power-series
presentation. -/
def ofSurjective (f : RestrictedPowerSeries ι A →ₐ[A] B) (hf : Function.Surjective f) :
    Presentation A B ι where
  toAlgHom := f
  surjective := hf

/-- Convert a closed restricted-power-series quotient isomorphism into a
restricted presentation. -/
def ofClosedQuotient {K : Ideal (RestrictedPowerSeries ι A)}
    (e : RestrictedPowerSeries ι A ⧸ K ≃+* B)
    (he : ∀ a : A,
      e (algebraMap A (RestrictedPowerSeries ι A ⧸ K) a) = algebraMap A B a) :
    Presentation A B ι :=
  ofSurjective
    ((AlgEquiv.ofRingEquiv he).toAlgHom.comp (Ideal.Quotient.mkₐ A K))
    ((AlgEquiv.ofRingEquiv he).surjective.comp Ideal.Quotient.mk_surjective)

variable (P : Presentation A B ι)

/-- The kernel `J` of a restricted-power-series presentation. -/
abbrev ker : Ideal (RestrictedPowerSeries ι A) :=
  RingHom.ker P.toAlgHom

/-- The algebra extension associated with a restricted-power-series
presentation, used to view `J / J²` as a `B`-module. -/
def toExtension : Algebra.Extension A B :=
  Algebra.Extension.ofSurjective P.toAlgHom P.surjective

/-- A restricted-power-series presentation is a surjective `A`-algebra map from
`A{x_ι}`. -/
theorem toAlgHom_surjective : Function.Surjective P.toAlgHom := sorry

/-- The kernel of `toExtension` recovers the kernel of the presentation map. -/
theorem toExtension_ker : P.toExtension.ker = P.ker := sorry

/-- The structure map of `ofQuotient J` is the canonical quotient map. -/
theorem ofQuotient_toAlgHom (J : Ideal (RestrictedPowerSeries ι A))
    (x : RestrictedPowerSeries ι A) :
    (ofQuotient J).toAlgHom x = Ideal.Quotient.mk J x := sorry

/-- The structure map of `ofSurjective f hf` is `f`. -/
theorem ofSurjective_toAlgHom (f : RestrictedPowerSeries ι A →ₐ[A] B)
    (hf : Function.Surjective f) :
    (ofSurjective f hf).toAlgHom = f := sorry

/-- The structure map of `ofClosedQuotient` is the given equivalence composed
with the canonical quotient map. -/
theorem ofClosedQuotient_toAlgHom {K : Ideal (RestrictedPowerSeries ι A)}
    (e : RestrictedPowerSeries ι A ⧸ K ≃+* B)
    (he : ∀ a : A,
      e (algebraMap A (RestrictedPowerSeries ι A ⧸ K) a) = algebraMap A B a)
    (x : RestrictedPowerSeries ι A) :
    (ofClosedQuotient e he).toAlgHom x =
      e (Ideal.Quotient.mk K x) := sorry

end Presentation

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]
variable {ι : Type u}
variable {B : Type u} [CommRing B] [Algebra A B]

/-- Partial derivatives of restricted power series commute with reduction
modulo open ideals. -/
theorem pderiv_compatible (i : ι) (f : RestrictedPowerSeries ι A) :
    Compatible fun J : OpenIdeal A ↦ MvPolynomial.pderiv i (f.1 J) := sorry

/-- The partial derivative of a restricted power series with respect to the
variable `i`, obtained componentwise from `MvPolynomial.pderiv`. -/
def pderiv (i : ι) :
    RestrictedPowerSeries ι A →ₗ[A] RestrictedPowerSeries ι A where
  toFun f := ⟨fun J ↦ MvPolynomial.pderiv i (f.1 J), pderiv_compatible i f⟩
  map_add' := sorry
  map_smul' := sorry

/-- Evaluating a restricted partial at an open ideal recovers the ordinary
polynomial partial of that component. -/
theorem pderiv_component (i : ι) (J : OpenIdeal A) (f : RestrictedPowerSeries ι A) :
    component J (pderiv i f) = MvPolynomial.pderiv i (component J f) := sorry

/-- Restricted partials extend ordinary polynomial partials along
`ofPolynomial`. -/
theorem pderiv_ofPolynomial (i : ι) (g : MvPolynomial ι A) :
    pderiv i (ofPolynomial g) = ofPolynomial (MvPolynomial.pderiv i g) := sorry

/-- The representative Jacobian on the kernel of a restricted presentation,
sending `g ∈ J` to the images of the restricted partials `∂g / ∂x_i`. -/
def jacobianOnKer (P : Presentation A B ι) :
    P.ker →ₗ[A] (ι → B) where
  toFun g i := P.toAlgHom (pderiv i (g : RestrictedPowerSeries ι A))
  map_add' := sorry
  map_smul' := sorry

/-- The representative Jacobian is given on kernel elements by restricted
partials. -/
theorem jacobianOnKer_apply (P : Presentation A B ι) (g : P.ker) (i : ι) :
    jacobianOnKer P g i = P.toAlgHom (pderiv i (g : RestrictedPowerSeries ι A)) :=
  sorry

/-- The representative Jacobian vanishes on `J²`. -/
theorem jacobianOnKer_square (P : Presentation A B ι) :
    ((P.ker • ⊤ : Submodule (RestrictedPowerSeries ι A) P.ker).restrictScalars A) ≤
      LinearMap.ker (jacobianOnKer P) := sorry

/-- The Jacobian of a restricted presentation, obtained by descending the
representative map on `J` through `J / J²`. -/
def jacobian [Fintype ι] (P : Presentation A B ι) :
    P.toExtension.Cotangent →ₗ[B] (ι → B) where
  toFun x :=
    let p := (P.ker • ⊤ : Submodule (RestrictedPowerSeries ι A) P.ker)
    Submodule.liftQ (p.restrictScalars A) (jacobianOnKer P) (jacobianOnKer_square P)
      ((Submodule.Quotient.restrictScalarsEquiv A p).symm
        (Algebra.Extension.Cotangent.val x))
  map_add' := sorry
  map_smul' := sorry

/-- The Jacobian sends the residue of `g ∈ J` to the images of the restricted
partials `∂g / ∂x_i`. -/
theorem jacobian_apply [Fintype ι] (P : Presentation A B ι)
    {g : RestrictedPowerSeries ι A} (hg : g ∈ P.ker) (i : ι) :
    jacobian P (Algebra.Extension.Cotangent.mk ⟨g, hg⟩) i =
      P.toAlgHom (pderiv i g) := sorry

/-- The two-term completed naive cotangent complex of a restricted
presentation, with degree-one term `J / J²`, degree-zero term `⊕ᵢ B dx_i`, and
differential the Jacobian of restricted partials. Source degrees `-1` and `0`
are encoded as homological degrees `1` and `0` on `ChainComplex ℕ`. -/
def complex [Fintype ι] (P : Presentation A B ι) :
    ChainComplex (ModuleCat B) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of B (ι → B))
    (ModuleCat.of B P.toExtension.Cotangent)
    (ModuleCat.ofHom (jacobian P))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, CategoryTheory.Limits.zero_comp⟩)

/-- The differential of the restricted naive cotangent complex in degrees
`1 → 0` is the Jacobian. -/
theorem complex_d_one_zero [Fintype ι] (P : Presentation A B ι) :
    (complex P).d 1 0 = ModuleCat.ofHom (jacobian P) := sorry

/-- The degree-zero component is the free `B`-module on the variables. -/
def componentZeroIso [Fintype ι] (P : Presentation A B ι) :
    (complex P).X 0 ≅ ModuleCat.of B (ι → B) :=
  Iso.refl _

/-- The degree-one component is the conormal module `J / J²`. -/
def componentOneIso [Fintype ι] (P : Presentation A B ι) :
    (complex P).X 1 ≅ ModuleCat.of B P.toExtension.Cotangent :=
  Iso.refl _

/-- Higher components of the restricted Jacobian complex are the zero object of
`ModuleCat`. -/
def componentSuccIsoUnit [Fintype ι] (P : Presentation A B ι) (n : ℕ) :
    (complex P).X (n + 2) ≅ ModuleCat.of B PUnit :=
  ChainComplex.mk'XIso
    (ModuleCat.of B (ι → B))
    (ModuleCat.of B P.toExtension.Cotangent)
    (ModuleCat.ofHom (jacobian P))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, CategoryTheory.Limits.zero_comp⟩)
    n

namespace Presentation

variable {ι' ι'' : Type u}
variable {P : Presentation A B ι} {Q : Presentation A B ι'} {T : Presentation A B ι''}

/-- A morphism of restricted-power-series presentations is an `A`-algebra map
of the restricted power series rings commuting with the two structure maps to
`B`. -/
structure Hom (P : Presentation A B ι) (Q : Presentation A B ι') where
  /-- The underlying `A`-algebra map `A{x_ι} →ₐ[A] A{y_ι'}`. -/
  toAlgHom : RestrictedPowerSeries ι A →ₐ[A] RestrictedPowerSeries ι' A
  /-- The algebra map commutes with the two structure maps to `B`. -/
  commutes : Q.toAlgHom.comp toAlgHom = P.toAlgHom

namespace Hom

/-- The identity morphism of a restricted-power-series presentation commutes
with the structure map to `B`. -/
theorem id_commutes (P : Presentation A B ι) :
    P.toAlgHom.comp (AlgHom.id A (RestrictedPowerSeries ι A)) = P.toAlgHom :=
  sorry

/-- The identity morphism of a restricted-power-series presentation. -/
protected def id (P : Presentation A B ι) : Hom P P where
  toAlgHom := AlgHom.id A (RestrictedPowerSeries ι A)
  commutes := id_commutes P

/-- A morphism of presentations is compatible with the two structure maps to
`B`. -/
theorem toAlgHom_commutes (f : Hom P Q) (x : RestrictedPowerSeries ι A) :
    Q.toAlgHom (f.toAlgHom x) = P.toAlgHom x :=
  sorry

/-- The image of the source variable `x_i` under a presentation morphism. -/
def val (f : Hom P Q) (i : ι) : RestrictedPowerSeries ι' A :=
  f.toAlgHom (ofPolynomial (MvPolynomial.X i))

/-- `val` is evaluation of the underlying algebra map on the source variable. -/
theorem val_apply (f : Hom P Q) (i : ι) :
    f.val i = f.toAlgHom (ofPolynomial (MvPolynomial.X i)) :=
  sorry

/-- The algebra-map compatibility needed to view a presentation morphism as a
morphism of extensions. -/
theorem toExtensionHom_commutes (f : Hom P Q) :
    (IsScalarTower.toAlgHom A Q.toExtension.Ring B).comp f.toAlgHom =
      (IsScalarTower.toAlgHom A B B).comp
        (IsScalarTower.toAlgHom A P.toExtension.Ring B) :=
  sorry

/-- The morphism of algebra extensions induced by a morphism of restricted
presentations. -/
def toExtensionHom (f : Hom P Q) : P.toExtension.Hom Q.toExtension :=
  Extension.Hom.ofAlgHom f.toAlgHom (toExtensionHom_commutes f)

/-- Compatibility of composed presentation morphisms with the structure maps to
`B`. -/
theorem comp_commutes (f : Hom Q T) (g : Hom P Q) :
    T.toAlgHom.comp (f.toAlgHom.comp g.toAlgHom) = P.toAlgHom :=
  sorry

/-- Composition of morphisms of restricted-power-series presentations. -/
def comp (f : Hom Q T) (g : Hom P Q) : Hom P T where
  toAlgHom := f.toAlgHom.comp g.toAlgHom
  commutes := comp_commutes f g

/-- The Jacobian matrix of a morphism of presentations, acting on the free
module of Kähler generators. -/
def jacobianOnVars [Fintype ι] (f : Hom P Q) : (ι → B) →ₗ[B] (ι' → B) :=
  LinearMap.pi fun j ↦
    ∑ i, LinearMap.smulRight (LinearMap.proj i) (Q.toAlgHom (pderiv j (f.val i)))

/-- The Jacobian of a presentation morphism is given on coordinates by
restricted partials of the images of the source variables. -/
theorem jacobianOnVars_apply [Fintype ι] (f : Hom P Q) (dx : ι → B) (j : ι') :
    jacobianOnVars f dx j = ∑ i, dx i * Q.toAlgHom (pderiv j (f.val i)) :=
  sorry

end Hom

end Presentation

variable {ι' : Type u}
variable {P : Presentation A B ι} {Q : Presentation A B ι'}

/-- The degree-one component of the chain map induced by a morphism of
presentations commutes with the Jacobian differentials. -/
theorem chainMap_one_zero_comm [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    ModuleCat.ofHom (Cotangent.map f.toExtensionHom) ≫ (complex Q).d 1 0 =
      (complex P).d 1 0 ≫ ModuleCat.ofHom (Presentation.Hom.jacobianOnVars f) :=
  sorry

/-- Higher components of the induced chain map are zero, and the resulting
squares commute. -/
theorem chainMap_succ_comm [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) (n : ℕ)
    (p :
      Σ' (zero : (complex P).X n ⟶ (complex Q).X n)
        (one : (complex P).X (n + 1) ⟶ (complex Q).X (n + 1)),
        one ≫ (complex Q).d (n + 1) n = (complex P).d (n + 1) n ≫ zero) :
    (0 : (complex P).X (n + 2) ⟶ (complex Q).X (n + 2)) ≫ (complex Q).d (n + 2) (n + 1) =
      (complex P).d (n + 2) (n + 1) ≫ p.2.1 :=
  sorry

/-- The map of restricted naive cotangent complexes induced by a morphism of
presentations, given on `J / J²` by the conormal map and on `dx_i` by the
Jacobian of the images of the variables. -/
def chainMap [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    complex P ⟶ complex Q :=
  ChainComplex.mkHom _ _
    (ModuleCat.ofHom (Presentation.Hom.jacobianOnVars f))
    (ModuleCat.ofHom (Cotangent.map f.toExtensionHom))
    (chainMap_one_zero_comm f)
    (fun n p ↦ ⟨0, chainMap_succ_comm f n p⟩)

/-- The degree-zero component of an induced chain map is the Jacobian of the
images of the variables. -/
theorem chainMap_f_zero [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    (chainMap f).f 0 = ModuleCat.ofHom (Presentation.Hom.jacobianOnVars f) :=
  sorry

/-- The degree-one component of an induced chain map is the induced conormal
map. -/
theorem chainMap_f_one [Fintype ι] [Fintype ι'] (f : Presentation.Hom P Q) :
    (chainMap f).f 1 = ModuleCat.ofHom (Cotangent.map f.toExtensionHom) :=
  sorry

end Algebra.NaiveCotangent.Restricted
