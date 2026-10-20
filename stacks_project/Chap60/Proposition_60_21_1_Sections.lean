module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Zero
public import stacks_project.Chap60.Lemma_60_17_2_Object
public import stacks_project.Chap60.Lemma_60_18_3_Site

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CompletedCris DividedPowers
open CategoryTheory.SimplicialObject.ZeroCoskeleton

universe u w

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type u} [CommRing C] [Algebra A C]
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J : (n : ℕ) → Ideal (tensorPowerCarrier A ι n))
variable (hJ : ∀ n, J n = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
variable (hIJ : ∀ n, Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J n)
variable (E : (n : ℕ) →
    DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) (J n) (hIJ n))
variable (hE : ∀ n, DividedPowerEnvelope.IsUniversal γ
    (algebraMap A (tensorPowerCarrier A ι n)) (hIJ n) (E n))
variable (N : ℕ → ℕ)
variable (hN : ∀ n, Ideal.span {(p : (E n).D)} ^ N n ≤ (E n).D.ideal)
variable (γhat : (n : ℕ) → DividedPowers (RingHom.ker
    (AdicCompletion.toQuotient (Ideal.span {(p : (E n).D)}) (E n).D.ideal (N n) (hN n))))
variable (hγhat : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γhat n)
    (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D)))
variable [HasLimits AddCommGrpCat.{w}]

/-- The completed envelope `D(n)` as an object of `Cris^∧(C/A)`. -/
noncomputable def affineCrisDn (n : ℕ) :
    CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil :=
  crystallineDnCrisObject p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)
    (N n) (hN n) (γhat n) (hγhat n)

/-- The completed envelope `D(n)` is the named `(n+1)`-fold coproduct envelope object. -/
theorem affineCrisDn_eq (n : ℕ) :
    affineCrisDn γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat n =
      crystallineDnCrisObject p I γ π hπ n hIC hpnil (J n) (hJ n) (hIJ n) (E n) (hE n)
        (N n) (hN n) (γhat n) (hγhat n) :=
  sorry

/-- Inverse-limit sections `M(B) = lim_e F(B_e)` of an abelian sheaf on chaotic `Cris(C/A)`. -/
noncomputable def affineCrisSectionsObj
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil) :
    AddCommGrpCat.{w} :=
  limit (stageAbelianSystem γ (algebraMap A C) hIC hpnil F B)

/-- Unfolding of inverse-limit sections as a limit of the `p`-adic stage system. -/
theorem affineCrisSectionsObj_eq
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (B : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil) :
    affineCrisSectionsObj γ hIC hpnil F B =
      limit (stageAbelianSystem γ (algebraMap A C) hIC hpnil F B) :=
  sorry

/-- The source modules `M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)`. -/
noncomputable def affineCrisSections
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (n : ℕ) : AddCommGrpCat.{w} :=
  affineCrisSectionsObj γ hIC hpnil F
    (affineCrisDn γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat n)

/-- `M(n)` is the inverse limit of the abelian stage system of `F` on `D(n)`. -/
theorem affineCrisSections_eq
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (n : ℕ) :
    affineCrisSections γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat F n =
      limit
        (stageAbelianSystem γ (algebraMap A C) hIC hpnil F
          (affineCrisDn γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat n)) :=
  sorry

/-- Identification of a `p`-adic stage ring with the corresponding quotient of `B`. -/
theorem pAdicQuotientRing_quotient_eq
    (X : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil) (e : ℕ) :
    pAdicQuotientRing γ (algebraMap A C) hIC hpnil X e =
      (X.B ⧸ (Ideal.span ({(p : X.B)} : Set X.B) ^
        pAdicExponent γ (algebraMap A C) hIC hpnil X e)) :=
  sorry

/-- The `p`-power ideal on the source stage is contained in the kernel of the
induced map to the target stage quotient. -/
theorem pAdicQuotientStage_ringHom_ker
    {X Y : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil}
    (u : X ⟶ Y) (e : ℕ) :
    Ideal.span ({(p : X.B)} : Set X.B) ^
        pAdicExponent γ (algebraMap A C) hIC hpnil X e ≤
      RingHom.ker
        ((pAdicQuotientMk γ (algebraMap A C) hIC hpnil Y e).toRingHom.comp
          u.map.toRingHom) :=
  sorry

/-- The ring map of `p`-adic stages induced by a completed crystalline morphism. -/
noncomputable def pAdicQuotientStage_ringHom
    {X Y : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil}
    (u : X ⟶ Y) (e : ℕ) :
    pAdicQuotientRing γ (algebraMap A C) hIC hpnil X e →+*
      pAdicQuotientRing γ (algebraMap A C) hIC hpnil Y e where
  toFun :=
    Equiv.cast (pAdicQuotientRing_quotient_eq γ hIC hpnil Y e).symm ∘
      (Ideal.Quotient.lift
          (Ideal.span ({(p : X.B)} : Set X.B) ^
            pAdicExponent γ (algebraMap A C) hIC hpnil X e)
          ((pAdicQuotientMk γ (algebraMap A C) hIC hpnil Y e).toRingHom.comp u.map.toRingHom)
          (pAdicQuotientStage_ringHom_ker γ hIC hpnil u e)) ∘
        Equiv.cast (pAdicQuotientRing_quotient_eq γ hIC hpnil X e)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The quotient of a completed crystalline morphism at a `p`-adic stage. -/
theorem pAdicQuotientStage_map_isDPMorphism
    {X Y : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil}
    (u : X ⟶ Y) (e : ℕ) :
    IsDPMorphism
      (pAdicQuotientRing γ (algebraMap A C) hIC hpnil X e).dividedPowers
      (pAdicQuotientRing γ (algebraMap A C) hIC hpnil Y e).dividedPowers
      (pAdicQuotientStage_ringHom γ hIC hpnil u e) :=
  sorry

/-- Induced map of `p`-adic stages along a morphism of completed crystalline objects. -/
noncomputable def pAdicQuotientStage_map
    {X Y : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil}
    (u : X ⟶ Y) (e : ℕ) :
    pAdicQuotientStage γ (algebraMap A C) hIC hpnil X e ⟶
      pAdicQuotientStage γ (algebraMap A C) hIC hpnil Y e :=
  { hom :=
      { map := DPMorphism.mk' (pAdicQuotientStage_map_isDPMorphism γ hIC hpnil u e)
        base_comm := sorry
        quotient_comm := sorry } }

/-- The stage systems are functorial in the completed crystalline object. -/
noncomputable def stageAbelianSystem_map
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    {X Y : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil} (u : X ⟶ Y) :
    stageAbelianSystem γ (algebraMap A C) hIC hpnil F X ⟶
      stageAbelianSystem γ (algebraMap A C) hIC hpnil F Y :=
  { app := fun e =>
      ((sheafToPresheaf (⊥ : GrothendieckTopology
            (crisOppSite γ (algebraMap A C) hIC hpnil))
          AddCommGrpCat.{w}).obj F).map
        ((eqToHom
            (show
              (opOp (DividedPowerThickening.Cris γ (algebraMap A C) hIC hpnil)).obj
                  ((pAdicQuotientSystem γ (algebraMap A C) hIC hpnil X).obj e) =
                op (op (pAdicQuotientStage γ (algebraMap A C) hIC hpnil X e.unop)) from
              sorry)) ≫
          op (op (pAdicQuotientStage_map γ hIC hpnil u e.unop)) ≫
            eqToHom
              (show
                op (op (pAdicQuotientStage γ (algebraMap A C) hIC hpnil Y e.unop)) =
                  (opOp (DividedPowerThickening.Cris γ (algebraMap A C) hIC hpnil)).obj
                    ((pAdicQuotientSystem γ (algebraMap A C) hIC hpnil Y).obj e) from
                sorry))
    naturality := fun {_ _} _ => sorry }

/-- Inverse-limit sections as a covariant functor of completed crystalline objects. -/
noncomputable def affineCrisSectionsFunctor
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w}) :
    CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil ⥤ AddCommGrpCat.{w} where
  obj B := affineCrisSectionsObj γ hIC hpnil F B
  map {B B'} f :=
    lim.map (stageAbelianSystem_map γ hIC hpnil F f)
  map_id := sorry
  map_comp := sorry

variable [HasBinaryProducts
  (CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)ᵒᵖ]

/-- Inverse-limit sections of `F`, viewed as a chaotic sheaf on the opposite of
`Cris^∧(C/A)`. -/
noncomputable def affineCrisCompletedSheaf
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w}) :
    Sheaf (⊥ : GrothendieckTopology
      (CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)ᵒᵖ)
      AddCommGrpCat.{w} where
  obj :=
    { obj := fun X =>
        (affineCrisSectionsFunctor γ hIC hpnil F).obj X.unop.unop
      map := fun {X Y} f =>
        (affineCrisSectionsFunctor γ hIC hpnil F).map f.unop.unop
      map_id := sorry
      map_comp := sorry }
  property := Presheaf.isSheaf_bot _

/-- The sheaf of inverse-limit sections evaluates as inverse-limit sections on the
double-unopposite completed object. -/
theorem affineCrisCompletedSheaf_obj
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (X : (CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)ᵒᵖᵒᵖ) :
    (affineCrisCompletedSheaf γ hIC hpnil F).obj.obj X =
      (affineCrisSectionsFunctor γ hIC hpnil F).obj X.unop.unop :=
  sorry

/-- The alternating coface cochain complex of inverse-limit sections of `F` on the
positive powers of `D` in `Cris^∧(C/A)`, whose homology is that of
`M(0) → M(1) → M(2) → ⋯`. -/
noncomputable def affineCrisSectionsComplex
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{w} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w}).obj
    ((selfProduct
        (Opposite.op (affineCrisDn γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat 0))).rightOp ⋙
      (sheafToPresheaf
          (⊥ : GrothendieckTopology
            (CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)ᵒᵖ)
          AddCommGrpCat.{w}).obj
        (affineCrisCompletedSheaf γ hIC hpnil F))

/-- The degree-`n` object of the sections complex is inverse-limit sections on the `n`-fold
power of `D`. -/
theorem affineCrisSectionsComplex_obj
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (n : ℕ) :
    IsIsomorphic ((affineCrisSectionsComplex γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat F).X n)
      (affineCrisSections γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat F n) :=
  sorry

/-- Homology of the inverse-limit cochain complex `M(*)`. -/
noncomputable def affineCrisSectionsComplex_homology
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (n : ℕ) : AddCommGrpCat.{w} :=
  (affineCrisSectionsComplex γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat F).homology n

/-- Unfolding of the homology of `M(*)`. -/
theorem affineCrisSectionsComplex_homology_eq
    (F : Sheaf (⊥ : GrothendieckTopology (crisOppSite γ (algebraMap A C) hIC hpnil))
      AddCommGrpCat.{w})
    (n : ℕ) :
    affineCrisSectionsComplex_homology γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat F n =
      (affineCrisSectionsComplex γ hIC hpnil π hπ J hJ hIJ E hE N hN γhat hγhat F).homology n :=
  sorry
