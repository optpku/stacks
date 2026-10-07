module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.GroupTheory.Torsion
public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor.Amplitude
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section HomologyVanishing

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]
variable [HasSheafify (smallEtaleTopology X) (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify ((smallEtaleTopology X).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))]

/-- Vanishing of homology outside a finite interval is equivalent to the pair of
canonical t-structure bounds `IsGE a` and `IsLE b`. -/
theorem isZero_homology_iff (E : EtaleDerived X Λ) (a b : ℤ) :
    IsGE E a ∧ IsLE E b ↔
      ∀ i : ℤ, ¬ (a ≤ i ∧ i ≤ b) →
        IsZero
          ((homologyFunctor
              (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) i).obj E) :=
  sorry

end HomologyVanishing

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify (smallEtaleTopology X.left) (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify ((smallEtaleTopology X.left).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
variable [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y)
    (smallEtaleTopology (Over.left P.obj.right))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y)
      (smallEtaleTopology (Over.left P.obj.right))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

namespace etaleDerivedLowerShriek

section PlusTorsion

variable [GrothendieckTopology.HasSheafCompose (smallEtaleTopology X.left)
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Lemma 63.10.2 (1): for a finite type separated morphism `X.hom` of
quasi-compact quasi-separated schemes, a ring `Λ`, and `E` in
`D⁺_tors(X_étale, Λ)` or in `D(X_étale, Λ)` when `Λ` is torsion, the maps
`H^i(Rf_!(τ_≤ a E) ⟶ Rf_!(E))` induced by `truncLEι a` are isomorphisms for
`i ≤ a`. -/
@[stacks 0G2A]
theorem truncLE_homologyMap_isIso
    (E : EtaleDerived X.left Λ)
    (hE : AddMonoid.IsTorsion Λ ∨
      (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n))
    (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((homologyFunctor
          (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
        ((etaleDerivedLowerShriek X P).map
          ((t.truncLEι a).app E))) :=
  sorry

/-- Lemma 63.10.2 (2): there is an integer `N`, independent of `E`, such that
the maps `H^i(Rf_!(E) ⟶ Rf_!(τ_≥ (b - N) E))` induced by `truncGEπ (b - N)`
are isomorphisms for `i ≥ b`. -/
@[stacks 0G2A]
theorem exists_truncGE_homologyMap_isIso :
    ∃ N : ℤ, ∀ (E : EtaleDerived X.left Λ)
      (hE : AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n))
      (b i : ℤ) (hi : b ≤ i),
      IsIso
        ((homologyFunctor
            (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
          ((etaleDerivedLowerShriek X P).map
            ((t.truncGEπ (b - N)).app E))) :=
  sorry

/-- Lemma 63.10.2 (3): there is an integer `N`, independent of `E`, such that
if `H^i(E)` vanishes off a finite interval `[a, b]`, then `H^i(Rf_!(E))`
vanishes off `[a, b + N]`. -/
@[stacks 0G2A]
theorem exists_isGE_isLE :
    ∃ N : ℤ, ∀ (E : EtaleDerived X.left Λ)
      (hE : AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n))
      (a b : ℤ),
      IsGE E a → IsLE E b →
        IsGE ((etaleDerivedLowerShriek X P).obj E) a ∧
          IsLE ((etaleDerivedLowerShriek X P).obj E) (b + N) :=
  sorry

/-- On objects with torsion cohomology sheaves, `Rf_!` preserves every lower
t-structure bound. -/
theorem isGE (E : EtaleDerived X.left Λ) (h_tors : etaleDerivedIsTorsion E)
    (a : ℤ) (ha : IsGE E a) :
    IsGE ((etaleDerivedLowerShriek X P).obj E) a :=
  sorry

/-- There is an integer `N`, independent of `E`, such that on the source domain
of Lemma 63.10.2, `Rf_!` shifts every upper t-structure bound by at most `N`. -/
theorem exists_isLE :
    ∃ N : ℤ, ∀ (E : EtaleDerived X.left Λ)
      (hE : AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n))
      (b : ℤ), IsLE E b →
      IsLE ((etaleDerivedLowerShriek X P).obj E) (b + N) :=
  sorry

end PlusTorsion

/-- Specialization of `truncLE_homologyMap_isIso` to a torsion coefficient ring,
valid on all of `D(X_étale, Λ)`. -/
theorem truncLE_homologyMap_isIso_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ)
    (E : EtaleDerived X.left Λ) (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((homologyFunctor
          (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
        ((etaleDerivedLowerShriek X P).map
          ((t.truncLEι a).app E))) :=
  sorry

/-- Specialization of `exists_truncGE_homologyMap_isIso` to a torsion
coefficient ring, valid on all of `D(X_étale, Λ)`. -/
theorem exists_truncGE_homologyMap_isIso_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ, ∀ (E : EtaleDerived X.left Λ) (b i : ℤ) (hi : b ≤ i),
      IsIso
        ((homologyFunctor
            (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
          ((etaleDerivedLowerShriek X P).map
            ((t.truncGEπ (b - N)).app E))) :=
  sorry

/-- Specialization of `exists_isGE_isLE` to a torsion coefficient ring, valid
on all of `D(X_étale, Λ)`. -/
theorem exists_isGE_isLE_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ, ∀ (E : EtaleDerived X.left Λ) (a b : ℤ),
      IsGE E a → IsLE E b →
        IsGE ((etaleDerivedLowerShriek X P).obj E) a ∧
          IsLE ((etaleDerivedLowerShriek X P).obj E) (b + N) :=
  sorry

/-- If `Λ` is torsion, then `Rf_!` preserves every lower t-structure bound. -/
theorem mapsGE (hΛ : AddMonoid.IsTorsion Λ) :
    Functor.TStructure.MapsGE
      (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)
      t t 0 :=
  sorry

/-- If `Λ` is torsion, then `Rf_!` has a uniform upper cohomological bound. -/
theorem mapsLE (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ,
      Functor.TStructure.MapsLE
        (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)
        t t N :=
  sorry

/-- If `Λ` is torsion, then `Rf_!` has cohomological amplitude `[0, N]` for some
integer `N`. -/
theorem exists_hasAmplitude (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ,
      Functor.TStructure.HasAmplitude
        (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)
        t t 0 N :=
  sorry

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
