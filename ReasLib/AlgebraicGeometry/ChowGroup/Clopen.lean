/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.BivariantClass.ComponentRestriction
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.OpenImmersion

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.BivariantClass.ComponentRestriction (over ι)

noncomputable section

universe u v

namespace AlgebraicGeometry.ChowGroup.Clopen

variable {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]

/-- Degreewise Chow homology of an open subscheme over the base. -/
abbrev homology (U : X.left.Opens) (n : ℤ) :=
  @RelativeChow S _ δ _ (over X U)
    (inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))) n

/-- Cycles of a fixed relative dimension on an open subscheme. -/
abbrev cycles (U : X.left.Opens) (n : ℤ) :=
  CycleGroup U.toScheme ((U.ι ≫ X.hom).relativeDimensionFunction δ) n

/-- Rational boundaries among cycles of a fixed degree on an open subscheme. -/
abbrev boundaries (U : X.left.Opens) (n : ℤ) : AddSubgroup (cycles δ X U n) :=
  @RationalEquivalence.boundaries U.toScheme
    (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ X.hom))
    ((U.ι ≫ X.hom).relativeDimensionFunction δ) inferInstance n

/-- The inclusion of a clopen subscheme is proper. -/
theorem inclusion_isProper (U : X.left.Opens) (hU : IsClosed (U : Set X.left)) :
    IsProper (ι X U).left := by
  change IsProper U.ι
  letI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι (by simpa only [U.range_ι] using hU)
  infer_instance

/-- Restriction of a homogeneous Chow class to an open subscheme. -/
def restrict (U : X.left.Opens) (n : ℤ) :
    RelativeChow δ X n →+ homology δ X U n :=
  (AddEquiv.cast (by simp : n + (0 : ℕ) = n)).toAddMonoidHom.comp
    (@ChowGroup.flatPullback S _ δ _ (over X U) X
      (inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))) _
      (ι X U) 0 (inferInstanceAs (Flat U.ι))
      (inferInstanceAs (RelativeDimension U.ι 0)) n)

private def pushCycles {A B : Over S} [LocallyOfFiniteType A.hom]
    [LocallyOfFiniteType B.hom] (f : A ⟶ B) [IsProper f.left] (n : ℤ) :=
  CycleGroup.mapHom f.left (A.hom.relativeDimensionFunction δ)
    (B.hom.relativeDimensionFunction δ) n

variable {I : Type v} (U : I → X.left.Opens)
    (hclosed : ∀ i, IsClosed (U i : Set X.left))
    (hdisjoint : Pairwise fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left))
    (hcover : iSup U = ⊤)

/-- Extension by zero of degreewise cycles on clopen subschemes. -/
@[no_expose] def extendedCycles (n : ℤ)
    (a : ∀ i, cycles δ X (U i) n) (i : I) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) n :=
  @pushCycles S δ (over X (U i)) X
    (inferInstanceAs (LocallyOfFiniteType ((U i).ι ≫ X.hom))) _ (ι X (U i))
    (inclusion_isProper X (U i) (hclosed i)) n (a i)

include hdisjoint hcover in
/-- Extended cycles on a disjoint clopen cover form a locally finite family. -/
theorem assembledCycles_locallyFinite (n : ℤ)
    (a : ∀ i, cycles δ X (U i) n) :
    LocallyFinite fun i ↦
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
        (extendedCycles δ X U hclosed n a i)).support := by
  have hU : LocallyFinite fun i ↦ (U i : Set X.left) := by
    intro x
    have hx : x ∈ iSup U := by
      rw [hcover]
      trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨(U i : Set X.left), (U i).isOpen.mem_nhds hxi, ?_⟩
    refine (Set.finite_singleton i).subset ?_
    rintro j ⟨y, hyj, hyi⟩
    by_contra hji
    exact Set.disjoint_left.mp (hdisjoint hji) hyj hyi
  apply hU.subset
  intro i x hx
  change (∑ᶠ y ∈ (U i).ι.base ⁻¹' {x},
    (a i).1 y * (AlgebraicCycle.mapCoeff (U i).ι
      (((U i).ι ≫ X.hom).relativeDimensionFunction δ)
      (X.hom.relativeDimensionFunction δ) y : ℤ)) ≠ 0 at hx
  obtain ⟨y, hy, _⟩ := exists_ne_zero_of_finsum_mem_ne_zero hx
  have hyx : (U i).ι y = x := hy
  rw [← hyx]
  exact y.property

/-- The locally finite sum of cycles extended from a disjoint clopen cover. -/
def assembleCycles (n : ℤ)
    (a : ∀ i, cycles δ X (U i) n) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) n :=
  CycleGroup.locallyFiniteSum (X.hom.relativeDimensionFunction δ) n
    (extendedCycles δ X U hclosed n a)
    (assembledCycles_locallyFinite δ X U hclosed hdisjoint hcover n a)

/-- Assembly of zero cycles is zero. -/
theorem assembleCycles_zero (n : ℤ) :
    assembleCycles δ X U hclosed hdisjoint hcover n 0 = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (∑ᶠ i, CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
    (extendedCycles δ X U hclosed n 0 i) x) = 0
  have hzero (i : I) :
      CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
          (extendedCycles δ X U hclosed n 0 i) x = 0 := by
    letI : IsProper (ι X (U i)).left := inclusion_isProper X (U i) (hclosed i)
    change CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
      (pushCycles δ (ι X (U i)) n (0 : cycles δ X (U i) n)) x = 0
    have hz : pushCycles δ (ι X (U i)) n (0 : cycles δ X (U i) n) = 0 := by
      exact CycleGroup.mapValue_zero _ _ _ _
    rw [hz]
    rfl
  simp_rw [hzero]
  simp

/-- Assembly of cycles preserves addition. -/
theorem assembleCycles_add (n : ℤ)
    (a b : ∀ i, cycles δ X (U i) n) :
    assembleCycles δ X U hclosed hdisjoint hcover n (a + b) =
      assembleCycles δ X U hclosed hdisjoint hcover n a +
        assembleCycles δ X U hclosed hdisjoint hcover n b := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hfinite (c : ∀ i, cycles δ X (U i) n) :
      (Function.support fun i ↦
        CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
          (extendedCycles δ X U hclosed n c i) x).Finite :=
    (assembledCycles_locallyFinite δ X U hclosed hdisjoint hcover n c).point_finite x
  change (∑ᶠ i, CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
      (extendedCycles δ X U hclosed n (a + b) i) x) =
    (∑ᶠ i, CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
      (extendedCycles δ X U hclosed n a i) x) +
    ∑ᶠ i, CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
      (extendedCycles δ X U hclosed n b i) x
  have hadd (i : I) :
      CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
          (extendedCycles δ X U hclosed n (a + b) i) x =
        CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
          (extendedCycles δ X U hclosed n a i) x +
        CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
          (extendedCycles δ X U hclosed n b i) x := by
    letI : IsProper (ι X (U i)).left := inclusion_isProper X (U i) (hclosed i)
    change CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
      (pushCycles δ (ι X (U i)) n (a i + b i)) x =
      CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
        (pushCycles δ (ι X (U i)) n (a i)) x +
      CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction δ) n
        (pushCycles δ (ι X (U i)) n (b i)) x
    have hadd' : pushCycles δ (ι X (U i)) n (a i + b i) =
        pushCycles δ (ι X (U i)) n (a i) + pushCycles δ (ι X (U i)) n (b i) := by
      exact CycleGroup.mapValue_add _ _ _ _ _ _
    rw [hadd']
    rfl
  simp_rw [hadd]
  exact finsum_add_distrib (hfinite a) (hfinite b)

/-- The additive assembly map on cycles of a fixed degree. -/
def assembleCyclesHom (n : ℤ) :
    (∀ i, cycles δ X (U i) n) →+
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) n where
  toFun := assembleCycles δ X U hclosed hdisjoint hcover n
  map_zero' := assembleCycles_zero δ X U hclosed hdisjoint hcover n
  map_add' := assembleCycles_add δ X U hclosed hdisjoint hcover n

/-- Locally finite assembly of rational boundaries on clopen pieces is a rational boundary. -/
theorem assembleCycles_mem_boundaries (n : ℤ)
    (a : ∀ i, cycles δ X (U i) n)
    (ha : ∀ i, a i ∈ boundaries δ X (U i) n) :
    assembleCycles δ X U hclosed hdisjoint hcover n a ∈
      @RationalEquivalence.boundaries X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance n := sorry

/-- The product of the cycle-to-Chow quotient maps on the pieces of an open cover. -/
def componentChowClass (n : ℤ) :
    (∀ i, cycles δ X (U i) n) →+
    (∀ i, homology δ X (U i) n) where
  toFun a i := @chowClass (U i).toScheme
    (LocallyOfFiniteType.isLocallyNoetherian ((U i).ι ≫ X.hom))
    (((U i).ι ≫ X.hom).relativeDimensionFunction δ) inferInstance n (a i)
  map_zero' := by ext i; exact map_zero _
  map_add' a b := by ext i; exact map_add _ _ _

private theorem componentChowClass_surjective (n : ℤ) :
    Function.Surjective (componentChowClass δ X U n) := by
  intro a
  exact ⟨fun i ↦ Quotient.out (a i), funext fun i ↦ Quotient.out_eq (a i)⟩

private theorem assembly_ker (n : ℤ) :
    (componentChowClass δ X U n).ker ≤
      ((@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance n).comp
        (assembleCyclesHom δ X U hclosed hdisjoint hcover n)).ker := by
  intro a ha
  apply (@chowClass_eq_zero_iff X.left
    (LocallyOfFiniteType.isLocallyNoetherian X.hom)
    (X.hom.relativeDimensionFunction δ) inferInstance n _).mpr
  apply assembleCycles_mem_boundaries δ X U hclosed hdisjoint hcover n a
  intro i
  apply (@chowClass_eq_zero_iff (U i).toScheme
    (LocallyOfFiniteType.isLocallyNoetherian ((U i).ι ≫ X.hom))
    (((U i).ι ≫ X.hom).relativeDimensionFunction δ) inferInstance n _).mp
  exact congrFun ha i

/-- Assembly of Chow classes by quotient descent of locally finite cycle assembly. -/
@[no_expose] def assemble (n : ℤ) :
    (∀ i, homology δ X (U i) n) →+ RelativeChow δ X n :=
  (componentChowClass δ X U n).liftOfSurjective
    (componentChowClass_surjective δ X U n)
    ⟨(@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance n).comp
      (assembleCyclesHom δ X U hclosed hdisjoint hcover n),
      assembly_ker δ X U hclosed hdisjoint hcover n⟩

/-- Restricting an assembled Chow class recovers its prescribed class on each clopen piece. -/
theorem restrict_assemble (n : ℤ)
    (a : ∀ i, homology δ X (U i) n) (i : I) :
    restrict δ X (U i) n (assemble δ X U hclosed hdisjoint hcover n a) = a i := sorry

/-- A Chow class is recovered by assembling its restrictions to a disjoint clopen cover. -/
theorem assemble_restrict (n : ℤ) (a : RelativeChow δ X n) :
    assemble δ X U hclosed hdisjoint hcover n
      (fun i ↦ restrict δ X (U i) n a) = a := sorry

/-- Chow homology in each degree is the product of the Chow groups of a disjoint clopen cover. -/
def equiv (n : ℤ) :
    RelativeChow δ X n ≃+ (∀ i, homology δ X (U i) n) where
  toFun a i := restrict δ X (U i) n a
  invFun := assemble δ X U hclosed hdisjoint hcover n
  left_inv := assemble_restrict δ X U hclosed hdisjoint hcover n
  right_inv a := funext (restrict_assemble δ X U hclosed hdisjoint hcover n a)
  map_add' a b := funext fun i ↦ map_add (restrict δ X (U i) n) a b

end AlgebraicGeometry.ChowGroup.Clopen
