/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.CochainHomology
public import ReasLib.CategoryTheory.ShortComplex.Admissible

/-!
# Admissible Differential Graded Module Morphisms

Admissibility for differential graded modules means splitness after forgetting the differential
but retaining the externally graded right action.  This file specializes the generic
functor-relative admissibility API to that faithful forgetful functor and constructs the
connecting DG-module morphism attached to an explicit graded splitting.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Definition 22.7.1 (1) (09JT): a DG-module morphism is admissibly monic when it has a
retraction which is a morphism of externally graded right `A`-modules. -/
@[stacks 09JT]
abbrev IsAdmissibleMono {K L : DifferentialGradedModule.{u, w} A} (f : K ⟶ L) : Prop :=
  _root_.IsAdmissibleMono (forgetToGraded A) f

/-- Definition 22.7.1 (2) (09JT): a DG-module morphism is admissibly epic when it has a section
which is a morphism of externally graded right `A`-modules. -/
@[stacks 09JT]
abbrev IsAdmissibleEpi {L M : DifferentialGradedModule.{u, w} A} (g : L ⟶ M) : Prop :=
  _root_.IsAdmissibleEpi (forgetToGraded A) g

/-- Definition 22.7.1 (3) (09JT): a short complex of DG-modules is admissibly short exact
relative to the functor which forgets only the differential. -/
@[stacks 09JT]
abbrev IsAdmissibleShortExact
    (S : ShortComplex (DifferentialGradedModule.{u, w} A)) : Prop :=
  _root_.IsAdmissibleShortExact (forgetToGraded A) S

/-- The morphism property of DG-module maps which are split monic after forgetting only the
differential. -/
@[stacks 09JT "admissible monomorphisms as a morphism property"]
def admissibleMonomorphisms (A : CochainDGAlgebra.{u, v} R) :
    MorphismProperty (DifferentialGradedModule.{u, w} A) :=
  fun _ _ f ↦ IsAdmissibleMono f

/-- The morphism property of DG-module maps which are split epic after forgetting only the
differential. -/
@[stacks 09JT "admissible epimorphisms as a morphism property"]
def admissibleEpimorphisms (A : CochainDGAlgebra.{u, v} R) :
    MorphismProperty (DifferentialGradedModule.{u, w} A) :=
  fun _ _ f ↦ IsAdmissibleEpi f

/-- Admissible monomorphisms contain identities and are closed under composition. -/
instance admissibleMonomorphisms.isMultiplicative
    (A : CochainDGAlgebra.{u, v} R) :
    (admissibleMonomorphisms A :
      MorphismProperty (DifferentialGradedModule.{u, w} A)).IsMultiplicative := sorry

/-- Admissible monomorphisms are invariant under composition with isomorphisms. -/
instance admissibleMonomorphisms.respectsIso
    (A : CochainDGAlgebra.{u, v} R) :
    (admissibleMonomorphisms A :
      MorphismProperty (DifferentialGradedModule.{u, w} A)).RespectsIso := sorry

/-- Admissible epimorphisms contain identities and are closed under composition. -/
instance admissibleEpimorphisms.isMultiplicative
    (A : CochainDGAlgebra.{u, v} R) :
    (admissibleEpimorphisms A :
      MorphismProperty (DifferentialGradedModule.{u, w} A)).IsMultiplicative := sorry

/-- Admissible epimorphisms are invariant under composition with isomorphisms. -/
instance admissibleEpimorphisms.respectsIso
    (A : CochainDGAlgebra.{u, v} R) :
    (admissibleEpimorphisms A :
      MorphismProperty (DifferentialGradedModule.{u, w} A)).RespectsIso := sorry

/-- Admissible monomorphisms are exactly the maps admitting a graded `A`-linear retraction. -/
theorem isAdmissibleMono_iff_exists_retraction
    {K L : DifferentialGradedModule.{u, w} A} (f : K ⟶ L) :
    IsAdmissibleMono f ↔
      ∃ r : Graded.Hom L.toGraded K.toGraded,
        (forgetToGraded A).map f ≫ r = 𝟙 K.toGraded := sorry

/-- Admissible epimorphisms are exactly the maps admitting a graded `A`-linear section. -/
theorem isAdmissibleEpi_iff_exists_section
    {L M : DifferentialGradedModule.{u, w} A} (g : L ⟶ M) :
    IsAdmissibleEpi g ↔
      ∃ s : Graded.Hom M.toGraded L.toGraded,
        s ≫ (forgetToGraded A).map g = 𝟙 M.toGraded := sorry

/-- Lemma 22.19.1 (09K2): a DG-module map is admissibly monic when its underlying graded
`A`-module map is monic and its source is injective among graded `A`-modules. -/
@[stacks 09K2]
theorem isAdmissibleMono_of_mono_of_injective
    {I M : DifferentialGradedModule.{u, w} A} (f : I ⟶ M)
    [Mono ((forgetToGraded A).map f)] [Injective I.toGraded] :
    IsAdmissibleMono f := sorry

/-- Lemma 22.16.1 (09K0): a DG-module map is admissibly epic when its underlying graded
`A`-module map is epic and its target is projective among graded `A`-modules. -/
@[stacks 09K0]
theorem isAdmissibleEpi_of_epi_of_projective
    {M P : DifferentialGradedModule.{u, w} A} (f : M ⟶ P)
    [Epi ((forgetToGraded A).map f)] [Projective P.toGraded] :
    IsAdmissibleEpi f := sorry

namespace ShortComplex

/-- An explicit splitting of a DG-module short complex after forgetting only the differential.
Its retraction and section are therefore graded `A`-module maps. -/
@[stacks 09JT "graded splitting of a differential graded module short complex"]
abbrev GradedSplitting (S : ShortComplex (DifferentialGradedModule.{u, w} A)) :=
  (S.map (forgetToGraded A)).Splitting

/-- The degree-`n` component of the graded retraction in a chosen splitting. -/
def GradedSplitting.retractionApp
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) : S.X₂.X n →ₗ[R] S.X₁.X n :=
  sigma.r.hom n

/-- The degree-`n` component of the graded section in a chosen splitting. -/
def GradedSplitting.sectionApp
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) : S.X₃.X n →ₗ[R] S.X₂.X n :=
  sigma.s.hom n

/-- The graded retraction component is the corresponding component of `sigma.r`. -/
@[simp]
theorem GradedSplitting.retractionApp_eq
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) : sigma.retractionApp n = sigma.r.hom n := sorry

/-- The graded section component is the corresponding component of `sigma.s`. -/
@[simp]
theorem GradedSplitting.sectionApp_eq
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) : sigma.sectionApp n = sigma.s.hom n := sorry

/-- A graded `A`-module splitting gives a splitting of the underlying cochain short complex in
every degree, by forgetting the action from its retraction and section. -/
def GradedSplitting.toDegreewiseSplitting
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S) :
    CategoryTheory.ShortComplex.DegreewiseSplitting (S.map (forgetToComplex A)) :=
  fun n ↦
    { r := ModuleCat.ofHom (sigma.retractionApp n)
      s := ModuleCat.ofHom (sigma.sectionApp n)
      f_r := sorry
      s_g := sorry
      id := sorry }

/-- The underlying degreewise retraction is the chosen graded retraction component. -/
@[simp]
theorem GradedSplitting.toDegreewiseSplitting_r
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) :
    (sigma.toDegreewiseSplitting n).r = ModuleCat.ofHom (sigma.retractionApp n) := sorry

/-- The underlying degreewise section is the chosen graded section component. -/
@[simp]
theorem GradedSplitting.toDegreewiseSplitting_s
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) :
    (sigma.toDegreewiseSplitting n).s = ModuleCat.ofHom (sigma.sectionApp n) := sorry

end ShortComplex

/-- An admissible short exact sequence is equivalently a short exact sequence together with the
mere existence of a splitting by externally graded `A`-module maps. -/
theorem isAdmissibleShortExact_iff_nonempty_gradedSplitting
    (S : ShortComplex (DifferentialGradedModule.{u, w} A)) :
    IsAdmissibleShortExact S ↔
      S.ShortExact ∧ Nonempty (ShortComplex.GradedSplitting S) := sorry

/-- An explicit graded splitting and short exactness imply admissibility. -/
theorem isAdmissibleShortExact_of_gradedSplitting
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)}
    (hS : S.ShortExact) (sigma : ShortComplex.GradedSplitting S) :
    IsAdmissibleShortExact S := sorry

/-- Every admissible short exact sequence merely admits a graded `A`-module splitting. -/
theorem IsAdmissibleShortExact.nonempty_gradedSplitting
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)}
    (hS : IsAdmissibleShortExact S) :
    Nonempty (ShortComplex.GradedSplitting S) := sorry

namespace Graded.Hom

/-- Reindexing a degree-preserving graded map gives a homogeneous map of degree zero between the
corresponding differential graded modules. -/
def toGradedHomZero {M N : DifferentialGradedModule.{u, w} A}
    (f : Graded.Hom M.toGraded N.toGraded) : GradedHom A M N 0 :=
  ⟨fun n ↦ ModuleCat.castLinearMap (congrArg N.X (add_zero n).symm) (f.hom n), sorry⟩

/-- The degree-`n` component of the degree-zero homogeneous map is the original graded component
with its canonical target reindexing. -/
@[simp]
theorem toGradedHomZero_apply {M N : DifferentialGradedModule.{u, w} A}
    (f : Graded.Hom M.toGraded N.toGraded) (n : ℤ) :
    f.toGradedHomZero n =
      ModuleCat.castLinearMap (congrArg N.X (add_zero n).symm) (f.hom n) := sorry

/-- The target of a degree `-1` homogeneous map into `N[1]` is canonically `N` in the original
degree. -/
theorem shiftHomotopyTargetEq (N : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    N.toGraded.X n = (N[1]).X (n + (-1)) := sorry

/-- A degree-preserving graded map `M ⟶ N` is the same raw degree data as a degree `-1`
homogeneous map `M ⟶ N[1]`, the form used by homotopies between connecting morphisms. -/
def toShiftHomotopy {M N : DifferentialGradedModule.{u, w} A}
    (f : Graded.Hom M.toGraded N.toGraded) : GradedHom A M (N[1]) (-1) :=
  ⟨fun n ↦ ModuleCat.castLinearMap (shiftHomotopyTargetEq N n) (f.hom n), sorry⟩

/-- The shifted homotopy bridge retains the original graded component, up to the canonical
degree reindexing. -/
@[simp]
theorem toShiftHomotopy_apply {M N : DifferentialGradedModule.{u, w} A}
    (f : Graded.Hom M.toGraded N.toGraded) (n : ℤ) :
    f.toShiftHomotopy n =
      ModuleCat.castLinearMap (shiftHomotopyTargetEq N n) (f.hom n) := sorry

end Graded.Hom

namespace ShortComplex

/-- The unshifted degree-`n` coordinate `pi ∘ d ∘ s` of the connecting morphism attached
to a chosen graded splitting. -/
def GradedSplitting.connectingCoordinate
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) : S.X₃.X n →ₗ[R] S.X₁.X (n + 1) :=
  (sigma.retractionApp (n + 1)).comp ((S.X₂.d n).comp (sigma.sectionApp n))

/-- The connecting coordinate is section, differential, then retraction. -/
@[simp]
theorem GradedSplitting.connectingCoordinate_apply
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) (x : S.X₃.X n) :
    sigma.connectingCoordinate n x =
      sigma.retractionApp (n + 1) (S.X₂.d n (sigma.sectionApp n x)) := sorry

/-- The degree-one graded `A`-linear map whose coordinates are `pi ∘ d ∘ s`. -/
def GradedSplitting.connectingGradedHom
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S) :
    GradedHom A S.X₃ S.X₁ 1 :=
  ⟨sigma.connectingCoordinate, sorry⟩

/-- The homogeneous components of the connecting graded map are the explicit connecting
coordinates. -/
@[simp]
theorem GradedSplitting.connectingGradedHom_apply
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) : sigma.connectingGradedHom n = sigma.connectingCoordinate n := sorry

/-- The degree-one connecting graded map is closed. -/
theorem GradedSplitting.connectingGradedHom_closed
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S) :
    gradedHomDifferential 1 sigma.connectingGradedHom = 0 := sorry

/-- The connecting DG-module morphism `S.X₃ ⟶ S.X₁[1]` determined by a chosen graded
splitting.  Its underlying coordinates are explicitly `pi ∘ d ∘ s`. -/
@[stacks 09JU "connecting morphism of an admissible DG-module short exact sequence"]
def GradedSplitting.connectingHom
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S) :
    S.X₃ ⟶ S.X₁[1] :=
  closedGradedHomEquivShiftHom A S.X₃ S.X₁ 1
    ⟨sigma.connectingGradedHom, sigma.connectingGradedHom_closed⟩

/-- The connecting DG-module morphism has the explicit shifted coordinate induced by
`pi ∘ d ∘ s`. -/
@[simp]
theorem GradedSplitting.connectingHom_hom
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (sigma : GradedSplitting S)
    (n : ℤ) :
    sigma.connectingHom.hom n =
      ModuleCat.castLinearMap (DifferentialGradedModule.shift_X S.X₁ 1 n).symm
        (sigma.connectingCoordinate n) := sorry

/-- Short exactness of a DG-module short complex descends to its underlying cochain short
complex. -/
theorem shortExact_map_forgetToComplex
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)} (hS : S.ShortExact) :
    (S.map (forgetToComplex A)).ShortExact := sorry

/-- Admissibility supplies short exactness of the underlying cochain short complex. -/
theorem admissibleShortExact_map_forgetToComplex
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)}
    (hS : DifferentialGradedModule.IsAdmissibleShortExact S) :
    (S.map (forgetToComplex A)).ShortExact := sorry

/-- Lemma 22.7.2 (09JU): the cochain triangle built from the underlying degreewise splitting
has boundary map equal to the canonical boundary of the underlying short exact sequence.  Its
third map has the same explicit `pi ∘ d ∘ s` coordinates as `connectingHom`. -/
@[stacks 09JU]
theorem boundary_eq_connecting
    {S : ShortComplex (DifferentialGradedModule.{u, w} A)}
    (hS : DifferentialGradedModule.IsAdmissibleShortExact S)
    (sigma : GradedSplitting S) (i j : ℤ) (hij : i + 1 = j) :
    CochainComplex.homologyδOfTriangle
        (CochainComplex.triangleOfDegreewiseSplit
          (S.map (forgetToComplex A)) sigma.toDegreewiseSplitting) i j hij =
      (admissibleShortExact_map_forgetToComplex hS).δ i j hij := sorry

end ShortComplex

end DifferentialGradedModule
