/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.MorphismDatum
public import ReasLib.AlgebraicGeometry.Scheme.Module.ProjFromSections

/-!
# Morphisms defined by linear systems

A generating linear map from a vector space into the global sections of an invertible module
defines an explicit quotient, lift, and morphism to the projective scheme of the vector space.
The construction is compatible with subspaces and with homogeneous coordinates after choosing
a basis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The sheaf morphism adjoint to a bundled linear map into global sections. -/
noncomputable def evaluation
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    (Scheme.Modules.pullback X.hom).obj (moduleSheaf k V) ⟶ L :=
  Scheme.Modules.pullbackTildeHom X.hom (ModuleCat.of k V) L ψ

/-- A linear system generates an invertible module when its adjoint evaluation morphism is
epimorphic. -/
def Generates
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) : Prop :=
  Epi (evaluation X L ψ)

/-- Generation by a linear system is precisely epimorphicity of its adjoint evaluation map. -/
theorem generates_iff
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    Generates X L ψ ↔ Epi (evaluation X L ψ) :=
  Iff.rfl

/-- A generating linear system gives an explicit invertible quotient of the pullback of the
affine module sheaf. -/
noncomputable def quotient
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    CategoryTheory.InvertibleQuotient
      ((Scheme.Modules.pullback X.hom).obj (moduleSheaf k V)) where
  object := L
  isInvertible := inferInstance
  hom := evaluation X L ψ
  hom_epi := hψ

/-- The lift classified by the explicit invertible quotient of a generating linear system. -/
noncomputable def lift
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    Scheme.ProjectiveBundle.Lift (toSpec k V) X.hom :=
  (hP.liftEquiv X.hom).symm (quotient X L ψ hψ)

/-- The morphism defined by a generating linear system is the morphism underlying its classified
lift. -/
noncomputable def morphism
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    X.left ⟶ scheme k V :=
  (lift hP X L ψ hψ).hom

/-- A morphism has the linear-system specification when it underlies a lift classified by the
explicit quotient built from the given sections. -/
def MorphismSpec
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (φ : X.left ⟶ scheme k V) : Prop :=
  ∃ σ : Scheme.ProjectiveBundle.Lift (toSpec k V) X.hom,
    σ.hom = φ ∧ hP.liftEquiv X.hom σ = quotient X L ψ hψ

/-- The linear-system morphism specification is the equality under the chosen quotient
representation, together with the underlying morphism equality. -/
theorem morphismSpec_iff
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) (φ : X.left ⟶ scheme k V) :
    MorphismSpec hP X L ψ hψ φ ↔
      ∃ σ : Scheme.ProjectiveBundle.Lift (toSpec k V) X.hom,
        σ.hom = φ ∧ hP.liftEquiv X.hom σ = quotient X L ψ hψ :=
  Iff.rfl

/-- The explicitly constructed morphism is classified by the quotient of its generating linear
system. -/
theorem morphism_spec
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    MorphismSpec hP X L ψ hψ (morphism hP X L ψ hψ) := sorry

/-- The chosen projective-bundle representation classifies a unique morphism with the given
linear-system quotient. -/
theorem existsUnique_morphism
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    ∃! φ : X.left ⟶ scheme k V,
      MorphismSpec hP X L ψ hψ φ := sorry

/-- Pulling the tautological module back along the linear-system morphism yields the given
invertible module. -/
noncomputable def pullbackTautologicalSheafIso
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    (Scheme.Modules.pullback (morphism hP X L ψ hψ)).obj
        (tautologicalSheaf hP) ≅ L :=
  (hP.pullbackTautologicalIso X.hom (lift hP X L ψ hψ)).trans
    (eqToIso (congrArg CategoryTheory.InvertibleQuotient.object
      ((hP.liftEquiv X.hom).apply_symm_apply (quotient X L ψ hψ))))

/-- The map on global sections induced from the tautological quotient and its pullback
identification is the original bundled linear map. -/
theorem inducedLinearMap_eq
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    Scheme.Modules.pullbackTildeHomEquiv X.hom (ModuleCat.of k V) L
      ((Scheme.ProjectiveBundle.Lift.pullbackSourceIso
          (lift hP X L ψ hψ) (moduleSheaf k V)).inv ≫
        (Scheme.Modules.pullback (morphism hP X L ψ hψ)).map
          (Scheme.ProjectiveBundle.tautologicalQuotient
            (toSpec k V) hP).hom ≫
        (pullbackTautologicalSheafIso hP X L ψ hψ).hom) = ψ := sorry

/-- A generating subspace of global sections defines the projective morphism obtained from its
inclusion. -/
noncomputable def subspaceMorphism
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L))
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k W) (moduleSheaf k W))
    (hW : Generates X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype)) :
    X.left ⟶ scheme k W :=
  morphism hP X L (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) hW

/-- The morphism defined by a generating subspace is classified by its inclusion quotient. -/
theorem subspaceMorphism_spec
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L))
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k W) (moduleSheaf k W))
    (hW : Generates X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype)) :
    MorphismSpec hP X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) hW
      (subspaceMorphism X L W hP hW) := sorry

/-- The family of sections obtained by evaluating a linear map on a chosen basis. -/
def basisSections
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    Fin (n + 1) → Scheme.Hom.globalSectionsMod X.hom L :=
  fun i ↦ ψ (b i)

/-- A basis section is the image of the corresponding basis vector. -/
theorem basisSections_apply
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (i : Fin (n + 1)) :
    basisSections n b X L ψ i = ψ (b i) :=
  rfl

/-- A morphism to standard projective space has the basis specification when it is associated
to degree-one data whose coordinate sections are the images of the chosen basis vectors. -/
def BasisMorphismSpec
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (φ : X.left ⟶ ProjectiveSpace.scheme k n) : Prop :=
  ∃ τ : Proj.DegreeOneMorphismDatum (ProjectiveSpace.grading k n) X.left,
    Proj.DegreeOneMorphismDatum.AssociatedTo
        (ProjectiveSpace.grading k n) τ φ ∧
      ∃ e : RingedSpace.TensorPower.sheaf τ.lineBundle 1 ≅ L,
        ∀ i : Fin (n + 1),
          SheafOfModules.sectionsMap e.hom
            (RingedSpace.sectionFromTop
              (RingedSpace.TensorPower.sheaf τ.lineBundle 1)
              (tensorPowerSectionRingProj τ.lineBundle 1
                (τ.sectionMap
                  (DirectSum.of
                    (fun d : ℕ ↦ ProjectiveSpace.grading k n (d * 1)) 1
                    (Eq.mp
                      (congrArg
                        (fun d : ℕ ↦ ↥(ProjectiveSpace.grading k n d))
                        (Nat.mul_one 1).symm)
                      ⟨ProjectiveSpace.coordinate n i,
                        ProjectiveSpace.coordinate_mem_grading_one n i⟩))))) =
            RingedSpace.sectionFromTop L (basisSections n b X L ψ i)

/-- The basis-morphism specification is the existence of associated degree-one data and a
coordinate-compatible identification of its line bundle. -/
theorem basisMorphismSpec_iff
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (φ : X.left ⟶ ProjectiveSpace.scheme k n) :
    BasisMorphismSpec n b X L ψ φ ↔
      ∃ τ : Proj.DegreeOneMorphismDatum (ProjectiveSpace.grading k n) X.left,
        Proj.DegreeOneMorphismDatum.AssociatedTo
            (ProjectiveSpace.grading k n) τ φ ∧
          ∃ e : RingedSpace.TensorPower.sheaf τ.lineBundle 1 ≅ L,
            ∀ i : Fin (n + 1),
              SheafOfModules.sectionsMap e.hom
                (RingedSpace.sectionFromTop
                  (RingedSpace.TensorPower.sheaf τ.lineBundle 1)
                  (tensorPowerSectionRingProj τ.lineBundle 1
                    (τ.sectionMap
                      (DirectSum.of
                        (fun d : ℕ ↦ ProjectiveSpace.grading k n (d * 1)) 1
                        (Eq.mp
                          (congrArg
                            (fun d : ℕ ↦ ↥(ProjectiveSpace.grading k n d))
                            (Nat.mul_one 1).symm)
                          ⟨ProjectiveSpace.coordinate n i,
                            ProjectiveSpace.coordinate_mem_grading_one n i⟩))))) =
                RingedSpace.sectionFromTop L (basisSections n b X L ψ i) :=
  Iff.rfl

/-- After choosing a basis, the linear-system morphism followed by the basis comparison is the
corresponding morphism to standard projective space. -/
noncomputable def basisMorphism
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    X.left ⟶ ProjectiveSpace.scheme k n :=
  morphism hP X L ψ hψ ≫ basisComparison n b

/-- The explicit basis composite has the coordinate description determined by the basis
sections. -/
theorem basisMorphism_spec
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    BasisMorphismSpec n b X L ψ (basisMorphism hP n b X L ψ hψ) := sorry

/-- The basis-coordinate comparison diagram commutes by construction. -/
theorem morphism_basisComparison
    (hP : Scheme.ProjectiveBundle.Representation
      (toSpec k V) (moduleSheaf k V))
    (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (hψ : Generates X L ψ) :
    morphism hP X L ψ hψ ≫ basisComparison n b =
      basisMorphism hP n b X L ψ hψ :=
  rfl

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem
