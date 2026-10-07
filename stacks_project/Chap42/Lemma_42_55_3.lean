module

public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf.PerfectClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open Scheme.Hom.VirtualNormalBundle

/-- The pushed-forward structure sheaf of a regular closed immersion satisfies the
rank-bounded localized-Chern hypotheses in every positive degree. -/
theorem pushforwardStructureSheafSituation
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (t : ℕ) (ht : 0 < t) :
    @Situation S _ delta _ (Over.mk p) _ Z i hclosed
      (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X i
        (@instQuasiCompactOfIsClosedImmersion Z X i hclosed) inferInstance).obj
      t .rankBound := sorry

/-- Lemma 42.55.3 (1): the positive localized Chern classes of `i_* 𝒪_Z` below the
codimension of a regular closed immersion vanish. -/
@[stacks 0FEG]
theorem chernClass_pushforwardStructureSheaf_eq_zero
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory delta p)
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (t : ℕ) (ht : 0 < t) (htr : t < r) :
    let E := (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X i
      (@instQuasiCompactOfIsClosedImmersion Z X i hclosed) inferInstance).obj
    let setup := @pushforwardStructureSheafSituation S Z X _ delta _ p _ i _ hclosed _
      hX t ht
    @chernClass S _ delta _ (Over.mk p) _ Z i hclosed classes E
        (@Situation.perfect S _ delta _ (Over.mk p) _ Z i hclosed E t .rankBound setup) t
        (@Situation.offCenter S _ delta _ (Over.mk p) _ Z i hclosed E t .rankBound setup)
        (@Situation.finiteness S _ delta _ (Over.mk p) _ Z i hclosed E t .rankBound setup) =
      0 := sorry

/-- Lemma 42.55.3 (2): the degree-`r` localized Chern class of `i_* 𝒪_Z` is
`(-1)^(r - 1) * (r - 1)!` times the normal-sheaf bivariant class. -/
@[stacks 0FEG]
theorem chernClass_pushforwardStructureSheaf_eq_normalClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [hclosed : IsClosedImmersion i]
    [IsRegularImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (classes : ChernClass.Theory delta p)
    (hX : CompactSpace X ∨
      ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (hr : 0 < r)
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedSpecialization delta (i ≫ p) p i rfl (ofNormalSheaf i r e)) :
    let E := (@Scheme.DerivedQCoh.pushforwardStructureSheaf Z X i
      (@instQuasiCompactOfIsClosedImmersion Z X i hclosed) inferInstance).obj
    let setup := @pushforwardStructureSheafSituation S Z X _ delta _ p _ i _ hclosed _
      hX r hr
    @chernClass S _ delta _ (Over.mk p) _ Z i hclosed classes E
        (@Situation.perfect S _ delta _ (Over.mk p) _ Z i hclosed E r .rankBound setup) r
        (@Situation.offCenter S _ delta _ (Over.mk p) _ Z i hclosed E r .rankBound setup)
        (@Situation.finiteness S _ delta _ (Over.mk p) _ Z i hclosed E r .rankBound setup) =
      (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ)) •
        normalClass delta p i r e D := sorry

end AlgebraicGeometry.LocalizedChern
