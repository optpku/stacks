module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.HomologyBounds
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.RightDerived.Bounds
public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor.Amplitude
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Order.WithBotTop

/-!
# Cohomological bounds for derived étale lower shriek

Derived lower shriek along a separated finite-type morphism of quasi-compact
quasi-separated schemes has uniform truncation comparisons and interval bounds
on bounded-below torsion objects, and on all objects over a torsion ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open DerivedCategory DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [hXqc : CompactSpace X.left] [hXqs : QuasiSeparatedSpace X.left]

include hXqc hXqs
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

/-- Derived lower shriek sends the upper-truncation comparison to a homology
isomorphism in every degree at most the cutoff, on bounded-below torsion objects
or on arbitrary objects over a torsion coefficient ring. -/
theorem truncLE_homologyMap_isIso
    (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
    (hE : AddMonoid.IsTorsion Λ ∨
      (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n))
    (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((homologyFunctor
          (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
        ((etaleDerivedLowerShriek X P).map
          ((t.truncLEι a).app E))) :=
  sorry

/-- A uniform integer shift makes the lower-truncation comparison an
isomorphism on derived lower-shriek homology in every degree above the cutoff,
for bounded-below torsion objects or arbitrary objects over a torsion ring. -/
theorem exists_truncGE_homologyMap_isIso :
    ∃ N : ℤ, ∀ (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
      (hE : AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n))
      (b i : ℤ) (hi : b ≤ i),
      IsIso
        ((homologyFunctor
            (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
          ((etaleDerivedLowerShriek X P).map
            ((t.truncGEπ (b - N)).app E))) :=
  sorry

/-- Derived lower shriek has one cohomological bound, independent of the
compactification realization and of the admissible object. The same bound gives
both truncation comparisons and sends homology supported in an extended integer
interval `[a, b]` into `[a, b + N]`. The condition `i - N ≤ b` expresses the
shifted upper endpoint, including either infinite endpoint. -/
theorem exists_isGE_isLE :
    ∃ N : ℤ, ∀ (P : Compactification.Of Y X)
      [HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
      [∀ U : (Over.left P.obj.right).Etale,
        HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U)
          (ModuleCat.{u} Λ)]
      [HasDerivedCategory
        (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
      [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
        (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
      [(etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ)).Additive]
      [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
      [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
      [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (smallEtaleTopology Y)
          (smallEtaleTopology (Over.left P.obj.right))).Additive]
      [HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) (smallEtaleTopology Y)
            (smallEtaleTopology (Over.left P.obj.right))))
        (HomologicalComplex.quasiIso
          (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
          (ComplexShape.up ℤ))]
      (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
      (hE : AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n)),
      (∀ (a i : ℤ), i ≤ a →
        IsIso
          ((homologyFunctor
              (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
            ((etaleDerivedLowerShriek X P).map ((t.truncLEι a).app E)))) ∧
      (∀ (b i : ℤ), b ≤ i →
        IsIso
          ((homologyFunctor
              (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
            ((etaleDerivedLowerShriek X P).map ((t.truncGEπ (b - N)).app E)))) ∧
      (∀ (a b : EInt), a ≤ b →
        (∀ i : ℤ, ¬ (a ≤ (i : EInt) ∧ (i : EInt) ≤ b) →
          IsZero ((homologyFunctor
            (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) i).obj E)) →
        ∀ i : ℤ, ¬ (a ≤ (i : EInt) ∧ ((i - N : ℤ) : EInt) ≤ b) →
          IsZero ((homologyFunctor
            (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).obj
              ((etaleDerivedLowerShriek X P).obj E))) :=
  sorry

/-- On objects with torsion cohomology sheaves, derived lower shriek preserves
every lower t-structure bound. -/
theorem isGE
    (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
    (h_tors : etaleDerivedIsTorsion E)
    (a : ℤ) (ha : IsGE E a) :
    IsGE ((etaleDerivedLowerShriek X P).obj E) a :=
  sorry

/-- On bounded-below torsion objects, or on arbitrary objects over a torsion
ring, derived lower shriek shifts every upper t-structure bound by at most one
uniform integer. -/
theorem exists_isLE :
    ∃ N : ℤ, ∀ (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
      (hE : AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n))
      (b : ℤ), IsLE E b →
      IsLE ((etaleDerivedLowerShriek X P).obj E) (b + N) :=
  sorry

end PlusTorsion

/-- Over a torsion coefficient ring, the upper-truncation comparison induces
an isomorphism on derived lower-shriek homology below the cutoff for every object. -/
theorem truncLE_homologyMap_isIso_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ)
    (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
    (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((homologyFunctor
          (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
        ((etaleDerivedLowerShriek X P).map
          ((t.truncLEι a).app E))) :=
  sorry

/-- Over a torsion coefficient ring, one integer shift makes the
lower-truncation comparison an isomorphism on derived lower-shriek homology above
the cutoff for every object. -/
theorem exists_truncGE_homologyMap_isIso_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ, ∀ (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
      (b i : ℤ) (hi : b ≤ i),
      IsIso
        ((homologyFunctor
            (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
          ((etaleDerivedLowerShriek X P).map
            ((t.truncGEπ (b - N)).app E))) :=
  sorry

/-- Over a torsion coefficient ring, derived lower shriek sends every finite
cohomological interval `[a, b]` into `[a, b + N]` for one uniform integer `N`. -/
theorem exists_isGE_isLE_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ, ∀ (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
      (a b : ℤ),
      IsGE E a → IsLE E b →
        IsGE ((etaleDerivedLowerShriek X P).obj E) a ∧
          IsLE ((etaleDerivedLowerShriek X P).obj E) (b + N) :=
  sorry

/-- Over a torsion coefficient ring, derived lower shriek preserves every
lower t-structure bound. -/
theorem mapsGE (hΛ : AddMonoid.IsTorsion Λ) :
    Functor.TStructure.MapsGE
      (etaleDerivedLowerShriek X P (Λ := Λ))
      t t 0 :=
  sorry

/-- Over a torsion coefficient ring, derived lower shriek has a uniform
upper cohomological bound. -/
theorem mapsLE (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ,
      Functor.TStructure.MapsLE
        (etaleDerivedLowerShriek X P (Λ := Λ))
        t t N :=
  sorry

/-- Over a torsion coefficient ring, derived lower shriek has cohomological
amplitude `[0, N]` for some integer `N`. -/
theorem exists_hasAmplitude (hΛ : AddMonoid.IsTorsion Λ) :
    ∃ N : ℤ,
      Functor.TStructure.HasAmplitude
        (etaleDerivedLowerShriek X P (Λ := Λ))
        t t 0 N :=
  sorry

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
