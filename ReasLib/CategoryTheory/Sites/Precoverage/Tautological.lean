module

public import Mathlib.CategoryTheory.Sites.Coverage
public import ReasLib.CategoryTheory.Sites.Precoverage.Comparison

/-!
# Tautological closure of precoverages

This file owns the operation of closing a precoverage under tautological
equivalence of fixed-target covering families.  It is stated for bare
precoverages: coverage and pretopology presentations are downstream views.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory
namespace Precoverage

open SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C]

/-- Every cover of `K` can be replaced by a tautologically equivalent cover
of `L`.  This is the precoverage-level comparison relation underlying the
usual comparison of sheaf conditions. -/
def coversUpToTautologicalEquivalence (K L : Precoverage C) : Prop :=
  K.coversUpTo L fun {_} 𝒰 𝒱 ↦ TautologicallyEquivalent 𝒰 𝒱

/-- Replacing every `K`-cover by a tautologically equivalent `L`-cover
induces an inclusion of the generated Grothendieck topologies. -/
theorem toGrothendieck_le_of_tautological_covers
    {K L : Precoverage C} (h : K.coversUpToTautologicalEquivalence L) :
    K.toGrothendieck ≤ L.toGrothendieck := sorry

/-- A sheaf for `L` is a sheaf for `K` when each `K`-cover can be replaced by
a tautologically equivalent `L`-cover. -/
theorem isSheaf_of_tautological_covers
    {K L : Precoverage C} {P : Cᵒᵖ ⥤ Type w}
    (h : K.coversUpToTautologicalEquivalence L)
    (hP : Presheaf.IsSheaf L.toGrothendieck P) :
    Presheaf.IsSheaf K.toGrothendieck P := sorry

/-- Mutual tautological replacement of covering families gives equivalent
set-valued sheaf conditions. -/
theorem isSheaf_iff_of_mutual_tautological_covers
    {K L : Precoverage C} {P : Cᵒᵖ ⥤ Type w}
    (hKL : K.coversUpToTautologicalEquivalence L)
    (hLK : L.coversUpToTautologicalEquivalence K) :
    Presheaf.IsSheaf K.toGrothendieck P ↔
      Presheaf.IsSheaf L.toGrothendieck P := sorry

/-- If `L` contains `K` and every `L`-cover is tautologically represented by
a `K`-cover, then the two precoverages generate the same topology. -/
theorem toGrothendieck_eq_of_le_of_tautological_covers
    {K L : Precoverage C} (hK : K ≤ L)
    (hL : L.coversUpToTautologicalEquivalence K) :
    L.toGrothendieck = K.toGrothendieck := sorry

/-- The tautological closure of a precoverage consists of all presieves
represented by a family tautologically equivalent to an original covering
family. -/
def tautologicalClosure (K : Precoverage C) : Precoverage C where
  coverings X :=
    { R : Presieve X |
        ∃ 𝒰 𝒱 : SemiRepresentableFamily.Over.{max u v} X,
          IsCovering K 𝒰 ∧ TautologicallyEquivalent 𝒰 𝒱 ∧ 𝒱.toPresieve = R }

/-- A fixed-target family is covering for the tautological closure precisely
when it is tautologically equivalent to an original covering family. -/
theorem isCovering_tautologicalClosure_iff
    {K : Precoverage C} {X : C}
    {𝒱 : SemiRepresentableFamily.Over.{max u v} X} :
    IsCovering K.tautologicalClosure 𝒱 ↔
      ∃ 𝒰 : SemiRepresentableFamily.Over.{max u v} X,
        IsCovering K 𝒰 ∧ TautologicallyEquivalent 𝒰 𝒱 := sorry

/-- Every precoverage is contained in its tautological closure. -/
theorem le_tautologicalClosure (K : Precoverage C) :
    K ≤ K.tautologicalClosure := sorry

/-- Tautological closure is monotone in the original precoverage. -/
theorem tautologicalClosure_mono {K L : Precoverage C} (hKL : K ≤ L) :
    K.tautologicalClosure ≤ L.tautologicalClosure := sorry

/-- A precoverage is tautologically closed if its covering families are closed
under tautological equivalence. -/
class IsTautologicallyClosed (K : Precoverage C) : Prop where
  /-- Covering status is preserved by tautological equivalence. -/
  isCovering_of_tautologicallyEquivalent :
    ∀ {X : C} {𝒰 𝒱 : SemiRepresentableFamily.Over.{max u v} X},
      IsCovering K 𝒰 → TautologicallyEquivalent 𝒰 𝒱 → IsCovering K 𝒱

/-- The tautological closure is tautologically closed. -/
instance tautologicalClosure_isTautologicallyClosed (K : Precoverage C) :
    K.tautologicalClosure.IsTautologicallyClosed where
  isCovering_of_tautologicallyEquivalent := sorry

/-- A tautologically closed enlargement contains the tautological closure of
every sub-precoverage. -/
theorem tautologicalClosure_le_of_le
    {K L : Precoverage C} [L.IsTautologicallyClosed] (hKL : K ≤ L) :
    K.tautologicalClosure ≤ L := sorry

/-- Tautological closure is idempotent. -/
theorem tautologicalClosure_idempotent (K : Precoverage C) :
    K.tautologicalClosure.tautologicalClosure = K.tautologicalClosure := sorry

/-- Tautological closure does not change the generated Grothendieck topology. -/
theorem tautologicalClosure_toGrothendieck (K : Precoverage C) :
    K.tautologicalClosure.toGrothendieck = K.toGrothendieck := sorry

/-- Isomorphism coverings are retained by tautological closure. -/
theorem mem_tautologicalClosure_of_isIso
    {K : Precoverage C} [K.HasIsos]
    {X Y : C} (f : Y ⟶ X) [IsIso f] :
    Presieve.singleton f ∈ K.tautologicalClosure X := sorry

/-- Tautological closure inherits isomorphism coverings. -/
instance tautologicalClosure_hasIsos
    (K : Precoverage C) [K.HasIsos] :
    K.tautologicalClosure.HasIsos where
  mem_coverings_of_isIso _ := sorry

/-- Tautological closure is stable under indexed composition whenever the
original precoverage is. -/
theorem comp_mem_tautologicalClosure
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderComposition]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ K.tautologicalClosure S)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ K.tautologicalClosure (X i)) :
    Presieve.ofArrows (fun p : Σ i, σ i ↦ Y p.1 p.2)
      (fun p ↦ g p.1 p.2 ≫ f p.1) ∈ K.tautologicalClosure S := sorry

/-- Tautological closure inherits indexed-composition stability. -/
instance tautologicalClosure_isStableUnderComposition
    (K : Precoverage C) [K.HasIsos] [K.IsStableUnderComposition] :
    K.tautologicalClosure.IsStableUnderComposition where
  comp_mem_coverings := sorry

/-- Tautological closure is stable under chosen pullback families whenever
the original precoverage is. -/
theorem mem_tautologicalClosure_of_isPullback
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderBaseChange]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ K.tautologicalClosure S)
    {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    Presieve.ofArrows P p₁ ∈ K.tautologicalClosure Y := sorry

/-- Tautological closure inherits chosen-base-change stability. -/
instance tautologicalClosure_isStableUnderBaseChange
    (K : Precoverage C) [K.HasIsos] [K.IsStableUnderBaseChange] :
    K.tautologicalClosure.IsStableUnderBaseChange where
  mem_coverings_of_isPullback := sorry

/-- Tautological closure inherits existence of pullbacks along its covering
presieves. -/
instance tautologicalClosure_hasPullbacks
    (K : Precoverage C) [K.HasPullbacks] :
    K.tautologicalClosure.HasPullbacks where
  hasPullbacks_of_mem := sorry

end Precoverage

namespace Coverage

variable {C : Type u} [Category.{v} C]

/-- The tautological closure of a coverage presentation generates the same
Grothendieck topology as the original coverage. -/
theorem tautologicalClosure_toGrothendieck (K : Coverage C) :
    K.toPrecoverage.tautologicalClosure.toGrothendieck = K.toGrothendieck := sorry

end Coverage
end CategoryTheory
