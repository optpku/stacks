/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic.Taylor
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Equivalence
public import Mathlib.RingTheory.AdicCompletion.Completeness

@[expose] public section

noncomputable section

set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory DividedPowerEnvelope DPPolynomial.DeRham
open Connection.Adic
open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
variable (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E')

variable [Algebra.Smooth A P']
variable (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')

namespace CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth

/-- Nilpotence in the distinguished quotient follows from a power containment for the crystalline envelope. -/
private def quotientNilpotent : IsNilpotent (p : E'.D ⧸ E'.D.ideal) :=
  let bound := DividedPowers.PAdic.pAdicCompletionIsCrisWedgeObject p A P' I γ C
    (algebraMap A C) π'.toRingHom π'.comp_algebraMap hIC J' hJ' hπ' hpnil E' hE'
  ⟨bound.choose,
    (map_pow (Ideal.Quotient.mk E'.D.ideal) (p : E'.D) bound.choose).symm.trans
      ((Ideal.Quotient.eq_zero_iff_mem).mpr
        (bound.choose_spec.2.choose
          (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : E'.D))) bound.choose)))⟩

/-- The coefficient action on the smooth envelope determined by its structural map. -/
private abbrev smoothAlgebra : Algebra A E'.D :=
  (E'.toD.comp (algebraMap A P')).toAlgebra

variable {p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'}

/-- Complete integrable quasi-nilpotent polynomial-envelope connections. -/
private abbrev polynomialCategory : Cat :=
  -- Local instance justification (noncanonical choice): the category uses the coefficient action selected by the polynomial envelope.
  letI := Coordinates.baseAlgebra R.E
  Connection.Adic.quasiNilpotentCategory (A := A) (δ := R.E.D.dividedPowers)
    (Coordinates.completedCoord R.E R.hE p)

/-- Polynomial connections relative to the explicit structural coefficient map. -/
private abbrev polynomialConnection (M : ModuleCat.{u} R.polyD) :=
  -- Local instance justification (noncanonical choice): relative connections use the polynomial envelope's structural coefficient map.
  letI := Coordinates.baseAlgebra R.E
  Connection.Adic A R.E.D R.E.D.dividedPowers p M

/-- Smooth connections relative to the explicit structural coefficient map. -/
private abbrev smoothConnection (M : ModuleCat.{u} R.smoothD) :=
  -- Local instance justification (noncanonical choice): relative connections use the smooth envelope's structural coefficient map.
  letI := smoothAlgebra I γ J' hIJ' E'
  Connection.Adic A E'.D E'.D.dividedPowers p M

/-- Actual completed scalar extension of a polynomial-envelope connection along the retract map. -/
private def forwardConnection (M : ModuleCat.{u} R.polyD)
    (conn : polynomialConnection R M) :
    smoothConnection R
      (completedScalarExtension R.a p M) :=
  Connection.Adic.baseChange
    (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    (E'.toD.comp (algebraMap A P')) R.E.D.dividedPowers E'.D.dividedPowers p
    (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    R.γbar R.γbar' R.γbar_extends R.γbar'_extends R.a R.a_base R.a_isDP M conn

/-- Actual completed scalar extension of a smooth-envelope connection along the section. -/
private def reverseConnection (M : ModuleCat.{u} R.smoothD)
    (conn : smoothConnection R M) :
    polynomialConnection R
      (completedScalarExtension R.b p M) :=
  Connection.Adic.baseChange
    (E'.toD.comp (algebraMap A P'))
    (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    E'.D.dividedPowers R.E.D.dividedPowers p
    (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    R.γbar' R.γbar R.γbar'_extends R.γbar_extends R.b R.b_base R.b_isDP M conn

/-- A smooth connection is quasi-nilpotent when completed pullback along the section is polynomially quasi-nilpotent. -/
def IsQuasiNilpotent (M : ModuleCat.{u} R.smoothD)
    (conn : smoothConnection R M) : Prop :=
  -- Local instance justification (noncanonical choice): polynomial coordinate operators use the polynomial envelope's coefficient action.
  letI := Coordinates.baseAlgebra R.E
  IsTopologicallyQuasiNilpotent
    (reverseConnection R M conn)
    (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : R.polyD)))
    (Coordinates.completedCoord R.E R.hE p)

/-- The category of complete intrinsically integrable smooth-envelope connections satisfying section-pullback quasi-nilpotence. -/
def pairCategory : Cat :=
  -- Local instance justification (noncanonical choice): smooth connections use their envelope's specified coefficient action.
  letI := smoothAlgebra I γ J' hIJ' E'
  ⟨(Σ M : ModuleCat.{u} R.smoothD,
      {conn : Connection.Adic A E'.D E'.D.dividedPowers p M //
        IsAdicComplete (Ideal.span {(p : R.smoothD)}) M ∧
        Connection.Adic.IsIntegrable A E'.D E'.D.dividedPowers p conn ∧
        IsQuasiNilpotent R M conn}),
    { Hom := fun M N ↦ Connection.Adic.Hom M.2.val N.2.val
      id := fun M ↦ Connection.Adic.Hom.id M.2.val
      comp := fun f g ↦ Connection.Adic.Hom.comp f g
      id_comp := Connection.Adic.Hom.id_comp
      comp_id := Connection.Adic.Hom.comp_id
      assoc := Connection.Adic.Hom.assoc }⟩

/-- Construct a smooth connection pair from its actual coefficients and defining connection properties. -/
def pairOf (M : ModuleCat.{u} R.smoothD)
    (conn : smoothConnection R M)
    (hcomplete : IsAdicComplete (Ideal.span {(p : R.smoothD)}) M)
    (hintegrable :
      -- Local instance justification (noncanonical choice): smooth curvature uses its envelope's specified coefficient action.
      letI := smoothAlgebra I γ J' hIJ' E'
      Connection.Adic.IsIntegrable A E'.D E'.D.dividedPowers p conn)
    (hqn : IsQuasiNilpotent R M conn) :
    pairCategory R :=
  ⟨M, conn, hcomplete, hintegrable, hqn⟩

/-- Smooth pairs have complete coefficients, satisfy Leibniz, have intrinsic zero curvature, and are quasi-nilpotent after section pullback. -/
theorem pairCategory_spec
    (V : pairCategory R) :
    -- Local instance justification (noncanonical choice): the pair's connection and curvature use the smooth envelope's structural action.
    letI := smoothAlgebra I γ J' hIJ' E'
    IsAdicComplete (Ideal.span {(p : R.smoothD)}) V.1 ∧
    (∀ (r : R.smoothD) (m : V.1), V.2.val.toAddMonoidHom (r • m) =
      r • V.2.val.toAddMonoidHom m + AdicCompletion.of (Ideal.span {(p : R.smoothD)}) _
        (m ⊗ₜ[R.smoothD] completedDerivation A E'.D E'.D.dividedPowers p r)) ∧
    Connection.Adic.IsIntegrable A E'.D E'.D.dividedPowers p V.2.val ∧
    IsQuasiNilpotent R V.1 V.2.val := sorry

/-- Polynomial quasi-nilpotence is preserved by completed scalar extension to the smooth envelope. -/
theorem baseChange_quasiNilpotent
    (V : polynomialCategory R) :
    IsQuasiNilpotent R
      (completedScalarExtension R.a p V.1)
      (forwardConnection R V.1 V.2.val) := sorry

/-- Completed scalar extension assigns a smooth pair to a polynomial pair. -/
private def forwardObject (V : polynomialCategory R) : pairCategory R :=
  -- Local instance justification (noncanonical choice): the input curvature and connection use the polynomial envelope structural action.
  letI := Coordinates.baseAlgebra R.E
  -- Local instance justification (noncanonical choice): the output curvature and connection use the smooth envelope structural action.
  letI := smoothAlgebra I γ J' hIJ' E'
  pairOf R (completedScalarExtension R.a p V.1)
    (forwardConnection R V.1 V.2.val)
    (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : R.smoothD)))
    (Connection.Adic.baseChange_isIntegrable (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    (E'.toD.comp (algebraMap A P')) R.E.D.dividedPowers E'.D.dividedPowers p
    (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    R.γbar R.γbar' R.γbar_extends R.γbar'_extends R.a R.a_base R.a_isDP V.1 V.2.val V.2.property.choose_spec.1)
    (baseChange_quasiNilpotent R V)

/-- Completed scalar extension along the section assigns a polynomial pair to a smooth pair. -/
private def reverseObject (V : pairCategory R) : polynomialCategory R :=
  -- Local instance justification (noncanonical choice): the output connection and curvature use the polynomial envelope structural action.
  letI := Coordinates.baseAlgebra R.E
  -- Local instance justification (noncanonical choice): the input connection and curvature use the smooth envelope structural action.
  letI := smoothAlgebra I γ J' hIJ' E'
  ⟨completedScalarExtension R.b p V.1, reverseConnection R V.1 V.2.val,
    AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : R.polyD)),
    Connection.Adic.baseChange_isIntegrable (E'.toD.comp (algebraMap A P'))
    (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    E'.D.dividedPowers R.E.D.dividedPowers p
    (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    R.γbar' R.γbar R.γbar'_extends R.γbar_extends R.b R.b_base R.b_isDP V.1 V.2.val V.2.property.2.1,
    V.2.property.2.2⟩

/-- Horizontal maps extend along the polynomial-to-smooth completed-envelope map. -/
private def forwardMap {V W : polynomialCategory R} (g : V ⟶ W) :
    forwardObject R V ⟶ forwardObject R W :=
  -- Local instance justification (noncanonical choice): source horizontal maps use the polynomial envelope structural action.
  letI := Coordinates.baseAlgebra R.E
  -- Local instance justification (noncanonical choice): target horizontal maps use the smooth envelope structural action.
  letI := smoothAlgebra I γ J' hIJ' E'
  Connection.Adic.baseChangeHom (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    (E'.toD.comp (algebraMap A P')) R.E.D.dividedPowers E'.D.dividedPowers p
    (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    R.γbar R.γbar' R.γbar_extends R.γbar'_extends R.a R.a_base R.a_isDP V.1 V.2.val W.2.val g

/-- Horizontal maps extend along the smooth-to-polynomial section. -/
private def reverseMap {V W : pairCategory R} (g : V ⟶ W) :
    reverseObject R V ⟶ reverseObject R W :=
  -- Local instance justification (noncanonical choice): target horizontal maps use the polynomial envelope structural action.
  letI := Coordinates.baseAlgebra R.E
  -- Local instance justification (noncanonical choice): source horizontal maps use the smooth envelope structural action.
  letI := smoothAlgebra I γ J' hIJ' E'
  Connection.Adic.baseChangeHom (E'.toD.comp (algebraMap A P'))
    (R.E.toD.comp (algebraMap A (MvPolynomial (polynomialIndex R.n) A)))
    E'.D.dividedPowers R.E.D.dividedPowers p
    (quotientNilpotent p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') (quotientNilpotent p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    R.γbar' R.γbar R.γbar'_extends R.γbar_extends R.b R.b_base R.b_isDP V.1 V.2.val W.2.val g

/-- Completed extension along the retract map preserves identity and composition of horizontal maps. -/
theorem baseChange_functorLaws :
    (∀ V : polynomialCategory R, forwardMap R (𝟙 V) = 𝟙 _) ∧
    (∀ {U V W : polynomialCategory R} (g : U ⟶ V) (h : V ⟶ W),
      forwardMap R (g ≫ h) = forwardMap R g ≫ forwardMap R h) := sorry

/-- Completed extension along the section preserves identity and composition of horizontal maps. -/
theorem reverseBaseChange_functorLaws :
    (∀ V : pairCategory R, reverseMap R (𝟙 V) = 𝟙 _) ∧
    (∀ {U V W : pairCategory R} (g : U ⟶ V) (h : V ⟶ W),
      reverseMap R (g ≫ h) = reverseMap R g ≫ reverseMap R h) := sorry

/-- The completed scalar-extension functor from polynomial to smooth connection pairs. -/
def baseChange : polynomialCategory R ⥤ pairCategory R :=
  { obj := forwardObject R
    map := forwardMap R
    map_id := (baseChange_functorLaws R).1
    map_comp := (baseChange_functorLaws R).2 }

/-- The completed scalar-extension functor along the section from smooth to polynomial pairs. -/
def reverseBaseChange : pairCategory R ⥤ polynomialCategory R :=
  { obj := reverseObject R
    map := reverseMap R
    map_id := (reverseBaseChange_functorLaws R).1
    map_comp := (reverseBaseChange_functorLaws R).2 }

/-- Forward base change has the actual completed tensor coefficients and the induced Leibniz connection. -/
theorem baseChange_obj (V : polynomialCategory R) :
    ((baseChange R).obj V).1 = completedScalarExtension R.a p V.1 ∧
    HEq ((baseChange R).obj V).2.val (forwardConnection R V.1 V.2.val) := sorry

/-- Reverse base change has the actual completed tensor coefficients and the induced Leibniz connection. -/
theorem reverseBaseChange_obj (V : pairCategory R) :
    ((reverseBaseChange R).obj V).1 = completedScalarExtension R.b p V.1 ∧
    HEq ((reverseBaseChange R).obj V).2.val (reverseConnection R V.1 V.2.val) := sorry

/-- The coefficient equivalence for the smooth round trip uses tensor associativity and the retract identity. -/
private def sectionCoefficientEquiv (V : pairCategory R) :
    (((reverseBaseChange R) ⋙ baseChange R).obj V).1 ≃ₗ[R.smoothD] V.1 :=
  let identify : completedScalarExtension (R.a.comp R.b) p V.1 ≃ₗ[R.smoothD]
      completedScalarExtension (RingHom.id R.smoothD) p V.1 :=
    Eq.mp (congrArg (fun f ↦ completedScalarExtension f p V.1 ≃ₗ[R.smoothD]
      completedScalarExtension (RingHom.id R.smoothD) p V.1) R.retract_left.symm)
      (LinearEquiv.refl R.smoothD _)
  (completedScalarExtensionAssoc R.b R.a p V.1).trans
    (identify.trans (completedScalarExtensionId p V.1 V.2.property.1))

/-- The smooth round-trip coefficient equivalences are horizontal in both directions and natural. -/
theorem sectionIso_laws :
    -- Local instance justification (noncanonical choice): smooth horizontal maps use the envelope's structural coefficient action.
    letI := smoothAlgebra I γ J' hIJ' E'
    let H := reverseBaseChange R ⋙ baseChange R
    (∀ (V : pairCategory R) m, V.2.val.toAddMonoidHom (sectionCoefficientEquiv R V m) =
      tensorMap (sectionCoefficientEquiv R V).toLinearMap ((H.obj V).2.val.toAddMonoidHom m)) ∧
    (∀ (V : pairCategory R) m, (H.obj V).2.val.toAddMonoidHom ((sectionCoefficientEquiv R V).symm m) =
      tensorMap (sectionCoefficientEquiv R V).symm.toLinearMap (V.2.val.toAddMonoidHom m)) ∧
    (∀ {V W : pairCategory R} (g : V ⟶ W),
      (sectionCoefficientEquiv R W).toLinearMap.comp (H.map g).toLinearMap =
        g.toLinearMap.comp (sectionCoefficientEquiv R V).toLinearMap) := sorry

/-- The smooth round trip is canonically isomorphic to the identity through actual completed tensor maps. -/
def sectionIso : reverseBaseChange R ⋙ baseChange R ≅ 𝟭 (pairCategory R) :=
  -- Local instance justification (noncanonical choice): smooth horizontal maps use the envelope's structural coefficient action.
  letI := smoothAlgebra I γ J' hIJ' E'
  let laws := sectionIso_laws R
  NatIso.ofComponents
    (fun V ↦
      { hom := Connection.Adic.Hom.of (sectionCoefficientEquiv R V).toLinearMap (laws.1 V)
        inv := Connection.Adic.Hom.of (sectionCoefficientEquiv R V).symm.toLinearMap (laws.2.1 V)
        hom_inv_id := Connection.Adic.Hom.ext (LinearMap.ext (sectionCoefficientEquiv R V).symm_apply_apply)
        inv_hom_id := Connection.Adic.Hom.ext (LinearMap.ext (sectionCoefficientEquiv R V).apply_symm_apply) })
    (fun g ↦ Connection.Adic.Hom.ext (laws.2.2 g))

/-- The polynomial round-trip coefficient equivalence is the convergent Taylor comparison after tensor associativity. -/
private def retractCoefficientEquiv (V : polynomialCategory R) :
    (((baseChange R) ⋙ reverseBaseChange R).obj V).1 ≃ₗ[R.polyD] V.1 :=
  -- Local instance justification (noncanonical choice): Taylor derivatives use the polynomial envelope's structural coefficient action.
  letI := Coordinates.baseAlgebra R.E
  let hc := V.2.property.choose
  let hi := V.2.property.choose_spec.1
  let hq := V.2.property.choose_spec.2
  let forward := Connection.Adic.taylorComparison R V.1 V.2.val hc hi hq
  let reverse := Connection.Adic.taylorComparisonInv R V.1 V.2.val hc hi hq
  let laws := Connection.Adic.taylorComparison_inverse R V.1 V.2.val hc hi hq
  let taylor : completedScalarExtension (R.b.comp R.a) p V.1 ≃ₗ[R.polyD] V.1 :=
    { toFun := reverse
      invFun := forward
      left_inv := laws.2
      right_inv := laws.1
      map_add' := reverse.map_add
      map_smul' := reverse.map_smul }
  (completedScalarExtensionAssoc R.a R.b p V.1).trans taylor

/-- The polynomial round-trip Taylor equivalences are horizontal in both directions and natural. -/
theorem retractIso_laws :
    -- Local instance justification (noncanonical choice): polynomial horizontal maps use the envelope's structural coefficient action.
    letI := Coordinates.baseAlgebra R.E
    let H := baseChange R ⋙ reverseBaseChange R
    (∀ (V : polynomialCategory R) m, V.2.val.toAddMonoidHom (retractCoefficientEquiv R V m) =
      tensorMap (retractCoefficientEquiv R V).toLinearMap ((H.obj V).2.val.toAddMonoidHom m)) ∧
    (∀ (V : polynomialCategory R) m, (H.obj V).2.val.toAddMonoidHom ((retractCoefficientEquiv R V).symm m) =
      tensorMap (retractCoefficientEquiv R V).symm.toLinearMap (V.2.val.toAddMonoidHom m)) ∧
    (∀ {V W : polynomialCategory R} (g : V ⟶ W),
      (retractCoefficientEquiv R W).toLinearMap.comp (H.map g).toLinearMap =
        g.toLinearMap.comp (retractCoefficientEquiv R V).toLinearMap) := sorry

/-- The polynomial round trip is isomorphic to the identity by convergent divided-power Taylor expansion. -/
def retractIso : baseChange R ⋙ reverseBaseChange R ≅ 𝟭 (polynomialCategory R) :=
  -- Local instance justification (noncanonical choice): polynomial horizontal maps use the envelope's structural coefficient action.
  letI := Coordinates.baseAlgebra R.E
  let laws := retractIso_laws R
  NatIso.ofComponents
    (fun V ↦
      { hom := Connection.Adic.Hom.of (retractCoefficientEquiv R V).toLinearMap (laws.1 V)
        inv := Connection.Adic.Hom.of (retractCoefficientEquiv R V).symm.toLinearMap (laws.2.1 V)
        hom_inv_id := Connection.Adic.Hom.ext (LinearMap.ext (retractCoefficientEquiv R V).symm_apply_apply)
        inv_hom_id := Connection.Adic.Hom.ext (LinearMap.ext (retractCoefficientEquiv R V).apply_symm_apply) })
    (fun g ↦ Connection.Adic.Hom.ext (laws.2.2 g))

/-- Completed scalar extension along a smooth completed-envelope retract is an equivalence of connection categories. -/
instance baseChange_isEquivalence : (baseChange R).IsEquivalence := sorry

variable {X : Scheme.{u}} (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ IS.subscheme) (eX : Spec (.of C) ≅ X)
variable (heX : eX.hom ≫ x₀ ≫ IS.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : IS = DividedPowers.affineIdeal (I := I))
variable (hγ : DividedPowers.IsDPMorphism γ
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)

/-- A quasi-coherent crystal determines its genuine smooth completed-envelope connection by polynomial inverse-limit coefficients and completed scalar extension. -/
def toConnectionPairs : quasiCoherentCrystals IS γS hc x₀ ⥤ pairCategory R :=
  Completed.toConnectionPairs p γ R.π R.hπ R.hJ hIC hpnil R.E R.hE
    IS γS hc x₀ eX heX hI hγ ⋙ baseChange R

/-- The canonical crystalline connection functor for a smooth presentation is an equivalence. -/
instance toConnectionPairs_isEquivalence :
    (toConnectionPairs R IS γS hc x₀ eX heX hI hγ).IsEquivalence := sorry

end CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth
