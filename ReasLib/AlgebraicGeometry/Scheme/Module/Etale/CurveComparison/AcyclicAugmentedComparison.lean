/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.MappedResolutionComparison
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace ActualAcyclicAugmented
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable {M : C} (K : CochainComplex C ℕ) (ι : M ⟶ K.X 0)
variable (hzero : ι ≫ K.d 0 1 = 0) [hmono : Mono ι]
variable (hexact0 : (ShortComplex.mk ι (K.d 0 1) hzero).Exact)
variable (hexact : ∀ n : ℕ,
    (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d n (n + 1) (n + 2))).Exact)
variable (J : InjectiveResolution M)

/-- Extend the actual target augmentation along the augmented complex's monomorphism. -/
def zero : K.X 0 ⟶ J.cocomplex.X 0 :=
  @Injective.factorThru _ _ _ _ _ _ (J.ι.f 0) ι hmono

/-- Lift the next differential using exactness and target injectivity. -/
def one : K.X 1 ⟶ J.cocomplex.X 1 :=
  hexact0.descToInjective (zero K ι J ≫ J.cocomplex.d 0 1) sorry

theorem zero_one : K.d 0 1 ≫ one K ι hzero hexact0 J =
    zero K ι J ≫ J.cocomplex.d 0 1 := sorry

/-- Successive comparison components use the specified exact complex. -/
def succ (n : ℕ) (g : K.X n ⟶ J.cocomplex.X n)
    (g' : K.X (n + 1) ⟶ J.cocomplex.X (n + 1))
    (w : K.d n (n + 1) ≫ g' = g ≫ J.cocomplex.d n (n + 1)) :
    Σ' g'' : K.X (n + 2) ⟶ J.cocomplex.X (n + 2),
      K.d (n + 1) (n + 2) ≫ g'' = g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  ⟨(hexact n).descToInjective (g' ≫ J.cocomplex.d (n + 1) (n + 2)) sorry, sorry⟩

/-- Actual recursive comparison from an exact augmented complex to an injective resolution. -/
def map : K ⟶ J.cocomplex :=
  CochainComplex.mkHom _ _ (zero K ι J) (one K ι hzero hexact0 J)
    (zero_one K ι hzero hexact0 J).symm
    (fun n ⟨g, g', w⟩ ↦ ⟨(succ K hexact J n g g' w.symm).1,
      (succ K hexact J n g g' w.symm).2.symm⟩)

theorem augmentation : ι ≫ (map K ι hzero hexact0 hexact J).f 0 = J.ι.f 0 := sorry

variable [HasInjectiveResolutions C]
variable (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

/-- Apply sections termwise to the specified comparison, then take homology. -/
def homologyMap (n : ℕ) :
    (((S.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n) ⟶
      (S.rightDerived n).obj M :=
  (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
    ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (map K ι hzero hexact0 hexact J)) ≫ (J.isoRightDerivedObj S n).inv

/-- The constructed map is invertible for an exact augmented complex of
sections-acyclic objects. This is a property of the explicit map. -/
theorem homologyMap_isIso
    (hacyclic : ∀ q n : ℕ, IsZero ((S.rightDerived (n + 1)).obj (K.X q))) (n : ℕ) :
    IsIso (homologyMap K ι hzero hexact0 hexact J S n) := sorry

/-- Compute derived sections using the specified acyclic resolution. -/
def homologyIso
    (hacyclic : ∀ q n : ℕ, IsZero ((S.rightDerived (n + 1)).obj (K.X q))) (n : ℕ) :=
  @asIso _ _ _ _ (homologyMap K ι hzero hexact0 hexact J S n)
    (homologyMap_isIso K ι hzero hexact0 hexact J S hacyclic n)

end ActualAcyclicAugmented
