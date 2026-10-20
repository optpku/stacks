module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.GradedPieces.BaseChange
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Functorial
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.FMap

/-!
# Naturality of projective-space twist cohomology

The standard cohomology descriptions of twisting sheaves are compatible with coefficient
homomorphisms and with multiplication by homogeneous polynomials.  The compatibility predicates
record the canonical Čech and cohomology maps together with one coherent family of the standard
identifications.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.twistingSheaf

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- Multiplication by a homogeneous polynomial gives the canonical morphism between the
corresponding twisting sheaves. -/
noncomputable def mulHomogeneous (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ grading R n m) :
    twistingSheaf R n d ⟶ twistingSheaf R n (d + (m : ℤ)) :=
  @Proj.AssociatedModule.map
    R (MvPolynomial (Fin (n + 1)) R)
      (MvPolynomial (Fin (n + 1)) R) (MvPolynomial (Fin (n + 1)) R)
    _ _ _ _ _ _ _ _ _
    (Submodule R (MvPolynomial (Fin (n + 1)) R)) _ _
    (grading R n) _
    (GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading (grading R n)) d)
    (GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading (grading R n)) (d + (m : ℤ)))
    (GradedModule.shiftDecomposition
      (DirectSum.Decomposition.natToIntGrading (grading R n)) d)
    (GradedModule.shiftDecomposition
      (DirectSum.Decomposition.natToIntGrading (grading R n)) (d + (m : ℤ)))
    inferInstance inferInstance
    (LinearMap.mulLeft (MvPolynomial (Fin (n + 1)) R) f)
    (fun i g hg ↦ by
      have hg' : g ∈ gradedPiece R n (i + d) :=
        (GradedModule.mem_shiftGrading_iff
          (DirectSum.Decomposition.natToIntGrading (grading R n)) d i).mp hg
      apply (GradedModule.mem_shiftGrading_iff
        (DirectSum.Decomposition.natToIntGrading (grading R n))
        (d + (m : ℤ)) i).mpr
      change f * g ∈ gradedPiece R n (i + (d + (m : ℤ)))
      simpa [add_assoc] using
        mul_mem_gradedPiece R n (i + d) m f g hf hg')

/-- On a standard coordinate chart, homogeneous twist multiplication is multiplication of the
representing homogeneous fraction by the given polynomial. -/
theorem mulHomogeneous_on_coordinate (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ grading R n m)
    (i : Fin (n + 1))
    (z : Proj.AssociatedModule.away (grading R n)
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading (grading R n)) d)
      (⟨coordinate (R := R) n i, coordinate_mem_grading_one n i⟩ : grading R n 1)) :
    (((mulHomogeneous n d m f hf).val.app
        (op (coordinateBasicOpen (R := R) n i : (scheme R n).Opens))).hom
      (Proj.AssociatedModule.awaySection (grading R n)
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading (grading R n)) d)
        (⟨coordinate (R := R) n i, coordinate_mem_grading_one n i⟩ : grading R n 1)
        Nat.zero_lt_one z)) =
      Proj.AssociatedModule.awaySection (grading R n)
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading (grading R n)) (d + (m : ℤ)))
        (⟨coordinate (R := R) n i, coordinate_mem_grading_one n i⟩ : grading R n 1)
        Nat.zero_lt_one
        (@Proj.AssociatedModule.localizedMap
          R (MvPolynomial (Fin (n + 1)) R)
            (MvPolynomial (Fin (n + 1)) R) (MvPolynomial (Fin (n + 1)) R)
          _ _ _ _ _ _ _ _ _
          (Submodule R (MvPolynomial (Fin (n + 1)) R)) _ _
          (grading R n) _
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading (grading R n)) d)
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading (grading R n)) (d + (m : ℤ)))
          (GradedModule.shiftDecomposition
            (DirectSum.Decomposition.natToIntGrading (grading R n)) d)
          (GradedModule.shiftDecomposition
            (DirectSum.Decomposition.natToIntGrading (grading R n)) (d + (m : ℤ)))
          inferInstance inferInstance
          (LinearMap.mulLeft (MvPolynomial (Fin (n + 1)) R) f)
          (fun j g hg ↦ by
            have hg' : g ∈ gradedPiece R n (j + d) :=
              (GradedModule.mem_shiftGrading_iff
                (DirectSum.Decomposition.natToIntGrading (grading R n)) d j).mp hg
            apply (GradedModule.mem_shiftGrading_iff
              (DirectSum.Decomposition.natToIntGrading (grading R n))
              (d + (m : ℤ)) j).mpr
            change f * g ∈ gradedPiece R n (j + (d + (m : ℤ)))
            simpa [add_assoc] using
              mul_mem_gradedPiece R n (j + d) m f g hf hg')
          (Submonoid.powers (coordinate (R := R) n i)) z) := sorry

set_option maxHeartbeats 2000000 in
/-- Fixed standard cohomology identifications are compatible with coefficient base change when
the cohomology map is computed from the coefficient-induced projective morphism and the pulled
back standard coordinate family. -/
def BaseChangeCompatibleWith (φ : R →+* R') (n : ℕ) (d : ℤ)
    (zeroIdent :
      Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0 ≅
        ModuleCat.of R (gradedPiece R n d))
    (topIdent :
      Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n ≅
        ModuleCat.of R (topCohomologyDual R n d)) : Prop :=
  let ψ := coefficientGradedRingHom φ n
  let g := (projMapMap ψ).toLRSHom.toShHom
  let V : ULift.{u} (Fin (n + 1)) → Opens (scheme R n) := fun i ↦
    (coordinateBasicOpen (R := R) n i.down : (scheme R n).Opens)
  let U : ULift.{u} (Fin (n + 1)) → Opens (projMapDomain ψ).toScheme := fun i ↦
    RingedSpace.preimageOpen g (V i)
  let F := (twistingSheaf R' n d).restrict (projMapDomain ψ).ι
  projMapDomain ψ = ⊤ ∧
    ∃ (hU : IsRefinement (fun i ↦ RingedSpace.preimageOpen g (V i)) U (fun i ↦ i))
      (θ : twistingSheaf R n d ⟶ (RingedSpace.Hom.pushforward g).obj F)
      (zeroCechSource :
        (forget₂ (ModuleCat R) AddCommGrpCat.{u}).obj
            (Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0) ≅
          RingedSpace.moduleCechCohomology V (twistingSheaf R n d) 0)
      (zeroCechTarget :
        (forget₂ (ModuleCat R') AddCommGrpCat.{u}).obj
            (Scheme.Hom.cohomology (toSpec R' n) (twistingSheaf R' n d) 0) ≅
          RingedSpace.moduleCechCohomology U F 0)
      (topCechSource :
        (forget₂ (ModuleCat R) AddCommGrpCat.{u}).obj
            (Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n) ≅
          RingedSpace.moduleCechCohomology V (twistingSheaf R n d) n)
      (topCechTarget :
        (forget₂ (ModuleCat R') AddCommGrpCat.{u}).obj
            (Scheme.Hom.cohomology (toSpec R' n) (twistingSheaf R' n d) n) ≅
          RingedSpace.moduleCechCohomology U F n)
      (zeroIdentTarget :
        Scheme.Hom.cohomology (toSpec R' n) (twistingSheaf R' n d) 0 ≅
          ModuleCat.of R' (gradedPiece R' n d))
      (topIdentTarget :
        Scheme.Hom.cohomology (toSpec R' n) (twistingSheaf R' n d) n ≅
          ModuleCat.of R' (topCohomologyDual R' n d)),
      let zeroCechMap :
          RingedSpace.moduleCechCohomology V (twistingSheaf R n d) 0 ⟶
            RingedSpace.moduleCechCohomology U F 0 :=
        RingedSpace.ModuleCech.FMap.cohomologyMap
          (X := (projMapDomain ψ).toScheme.toRingedSpace)
          (Y := (scheme R n).toRingedSpace)
          (I := ULift.{u} (Fin (n + 1))) (J := ULift.{u} (Fin (n + 1)))
          (G := twistingSheaf R n d) (F := F)
          g U V (fun i ↦ i) hU θ 0
      let topCechMap :
          RingedSpace.moduleCechCohomology V (twistingSheaf R n d) n ⟶
            RingedSpace.moduleCechCohomology U F n :=
        RingedSpace.ModuleCech.FMap.cohomologyMap
          (X := (projMapDomain ψ).toScheme.toRingedSpace)
          (Y := (scheme R n).toRingedSpace)
          (I := ULift.{u} (Fin (n + 1))) (J := ULift.{u} (Fin (n + 1)))
          (G := twistingSheaf R n d) (F := F)
          g U V (fun i ↦ i) hU θ n
      (∀ x : Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0,
        zeroIdentTarget.hom
            (zeroCechTarget.inv
              (zeroCechMap (zeroCechSource.hom x))) =
          gradedPieceBaseChange φ n d (zeroIdent.hom x)) ∧
      (∀ x : Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n,
        topIdentTarget.hom
            (topCechTarget.inv
              (topCechMap (topCechSource.hom x))) =
          topCohomologyDualBaseChange φ n d (topIdent.hom x))

/-- There are standard degree-zero and top-degree twist cohomology identifications compatible
with a given coefficient homomorphism. -/
def BaseChangeCompatible (φ : R →+* R') (n : ℕ) (d : ℤ) : Prop :=
    ∃ (zeroIdent :
        Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0 ≅
          ModuleCat.of R (gradedPiece R n d))
      (topIdent :
        Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n ≅
          ModuleCat.of R (topCohomologyDual R n d)),
      BaseChangeCompatibleWith φ n d zeroIdent topIdent

/-- Fixed standard degree-zero and top-degree cohomology identifications carry the cohomology
morphism induced by a homogeneous polynomial to multiplication and its contragredient. -/
def MulCompatibleWith (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ grading R n m)
    (zeroIdent :
      Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0 ≅
        ModuleCat.of R (gradedPiece R n d))
    (topIdent :
      Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n ≅
        ModuleCat.of R (topCohomologyDual R n d)) : Prop :=
  ∃ (zeroIdentShift :
        Scheme.Hom.cohomology (toSpec R n)
            (twistingSheaf R n (d + (m : ℤ))) 0 ≅
          ModuleCat.of R (gradedPiece R n (d + (m : ℤ))))
    (topIdentShift :
        Scheme.Hom.cohomology (toSpec R n)
            (twistingSheaf R n (d + (m : ℤ))) n ≅
          ModuleCat.of R (topCohomologyDual R n (d + (m : ℤ)))),
    (∀ x : Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0,
      zeroIdentShift.hom
          (((Scheme.Hom.cohomologyFunctor (toSpec R n) 0).map
            (mulHomogeneous n d m f hf)) x) =
        mulMap R n d m f hf (zeroIdent.hom x)) ∧
    (∀ x : Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n,
      topIdentShift.hom
          (((Scheme.Hom.cohomologyFunctor (toSpec R n) n).map
            (mulHomogeneous n d m f hf)) x) =
        mulDual R n d m f hf (topIdent.hom x))

/-- There are standard degree-zero and top-degree twist cohomology identifications under which
a homogeneous polynomial acts by multiplication and its contragredient. -/
def MulCompatible (n : ℕ) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ grading R n m) : Prop :=
    ∃ (zeroIdent :
        Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0 ≅
          ModuleCat.of R (gradedPiece R n d))
      (topIdent :
        Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n ≅
          ModuleCat.of R (topCohomologyDual R n d)),
      MulCompatibleWith n d m f hf zeroIdent topIdent

/-- Over positive-dimensional projective space, one pair of standard cohomology identifications
is simultaneously compatible with coefficient homomorphisms and homogeneous multiplication. -/
theorem cohomology_naturality_sharedIdentifications (φ : R →+* R')
    (n : ℕ) (hn : 0 < n)
    (d : ℤ) (m : ℕ) (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m) :
    ∃ (zeroIdent :
        Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) 0 ≅
          ModuleCat.of R (gradedPiece R n d))
      (topIdent :
        Scheme.Hom.cohomology (toSpec R n) (twistingSheaf R n d) n ≅
          ModuleCat.of R (topCohomologyDual R n d)),
      BaseChangeCompatibleWith φ n d zeroIdent topIdent ∧
        MulCompatibleWith n d m f hf zeroIdent topIdent := sorry

/-- For every coefficient homomorphism, standard degree-zero and top-degree projective twist
cohomology identifications commute with coefficient base change. -/
theorem cohomology_baseChange (φ : R →+* R') (n : ℕ) (hn : 0 < n) (d : ℤ) :
    BaseChangeCompatible φ n d := by
  obtain ⟨zeroIdent, topIdent, hBaseChange, _⟩ :=
    cohomology_naturality_sharedIdentifications φ n hn d 0 0 (Submodule.zero_mem _)
  exact ⟨zeroIdent, topIdent, hBaseChange⟩

/-- For positive-dimensional projective space, homogeneous multiplication acts by ordinary
multiplication on degree-zero cohomology and contragrediently on top cohomology. -/
theorem cohomology_mul_homogeneous (n : ℕ) (hn : 0 < n) (d : ℤ) (m : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ grading R n m) :
    MulCompatible n d m f hf := by
  obtain ⟨zeroIdent, topIdent, _, hMul⟩ :=
    cohomology_naturality_sharedIdentifications (RingHom.id R) n hn d m f hf
  exact ⟨zeroIdent, topIdent, hMul⟩

/-- Standard descriptions of twisting-sheaf cohomology are separately natural under coefficient
homomorphisms and under multiplication by homogeneous polynomials. -/
theorem cohomology_naturality (φ : R →+* R') (n : ℕ) (hn : 0 < n)
    (d : ℤ) (m : ℕ) (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ grading R n m) :
    BaseChangeCompatible φ n d ∧ MulCompatible n d m f hf :=
  ⟨cohomology_baseChange φ n hn d, cohomology_mul_homogeneous n hn d m f hf⟩

end AlgebraicGeometry.ProjectiveSpace.twistingSheaf
