module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Dualizing
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A chosen finite open cover of `X` whose members are separated over `S`. -/
structure FiniteSeparatedOpenCover {S X : Scheme.{u}} (f : X ⟶ S) where
  /-- The type indexing the chosen cover. -/
  index : Type u
  /-- The chosen cover has finitely many members. -/
  finiteIndex : Finite index
  /-- The open subschemes in the chosen cover. -/
  opens : index → X.Opens
  /-- The chosen opens cover `X`. -/
  iSup_opens : iSup opens = ⊤
  /-- Each member of the cover is separated over `S`. -/
  isSeparated (i : index) : IsSeparated ((opens i).ι ≫ f)

namespace FiniteSeparatedOpenCover

/-- Construct a finite separated open cover from an explicitly indexed family. -/
def ofFamily {S X : Scheme.{u}} (f : X ⟶ S) (ι : Type u) [Finite ι]
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hSeparated : ∀ i, IsSeparated ((U i).ι ≫ f)) :
    FiniteSeparatedOpenCover f :=
  { index := ι
    finiteIndex := inferInstance
    opens := U
    iSup_opens := hU
    isSeparated := hSeparated }

end FiniteSeparatedOpenCover

/-- Exceptional inverse-image functors, their right-adjoint properties, and their canonical
transition isomorphisms on a fixed finite separated open cover. This is ambient duality data,
independent of the complex constructed by gluing. -/
structure ExceptionalInverseImageSetup {S X : Scheme.{u}} (f : X ⟶ S)
    (cover : FiniteSeparatedOpenCover f) where
  /-- The exceptional inverse-image functor on a member of the chosen cover. -/
  exceptionalPullback (i : cover.index) :
    RingedSpace.ModuleDerived S.toRingedSpace ⥤
      RingedSpace.moduleDerivedOnOpen X.toRingedSpace (cover.opens i)
  /-- The chosen exceptional inverse image is right adjoint to derived pushforward. -/
  exceptionalPullbackAdjunction (i : cover.index) :
    RingedSpace.moduleDerivedPushforward ((cover.opens i).ι ≫ f).toShHom ⊣
      exceptionalPullback i
  /-- The canonical transition between exceptional pullbacks restricted to a common open. -/
  canonicalTransition (i j : cover.index) (W : X.Opens)
      (hWi : W ≤ cover.opens i) (hWj : W ≤ cover.opens j) :
    exceptionalPullback i ⋙
        RingedSpace.OpenSubspace.Restriction.derivedBetween X.toRingedSpace hWi ≅
      exceptionalPullback j ⋙
        RingedSpace.OpenSubspace.Restriction.derivedBetween X.toRingedSpace hWj
  /-- The canonical transition from a member of the cover to itself is the identity. -/
  canonicalTransition_self (i : cover.index) (W : X.Opens) (hWi : W ≤ cover.opens i) :
    canonicalTransition i i W hWi hWi = Iso.refl _
  /-- Canonical transitions satisfy the cocycle law on every common open. -/
  canonicalTransition_cocycle (i j k : cover.index) (W : X.Opens)
      (hWi : W ≤ cover.opens i) (hWj : W ≤ cover.opens j) (hWk : W ≤ cover.opens k) :
    canonicalTransition i j W hWi hWj ≪≫ canonicalTransition j k W hWj hWk =
      canonicalTransition i k W hWi hWk

namespace ExceptionalInverseImageSetup

/-- Construct the exceptional inverse-image setup from the coverwise functors, adjunctions, and
coherent canonical transitions. -/
def ofAdjunctions {S X : Scheme.{u}} (f : X ⟶ S)
    (cover : FiniteSeparatedOpenCover f)
    (exceptionalPullback : ∀ i : cover.index,
      RingedSpace.ModuleDerived S.toRingedSpace ⥤
        RingedSpace.moduleDerivedOnOpen X.toRingedSpace (cover.opens i))
    (exceptionalPullbackAdjunction : ∀ i : cover.index,
      RingedSpace.moduleDerivedPushforward ((cover.opens i).ι ≫ f).toShHom ⊣
        exceptionalPullback i)
    (canonicalTransition : ∀ (i j : cover.index) (W : X.Opens)
      (hWi : W ≤ cover.opens i) (hWj : W ≤ cover.opens j),
      exceptionalPullback i ⋙
          RingedSpace.OpenSubspace.Restriction.derivedBetween X.toRingedSpace hWi ≅
        exceptionalPullback j ⋙
          RingedSpace.OpenSubspace.Restriction.derivedBetween X.toRingedSpace hWj)
    (canonicalTransition_self : ∀ (i : cover.index) (W : X.Opens)
      (hWi : W ≤ cover.opens i),
      canonicalTransition i i W hWi hWi = Iso.refl _)
    (canonicalTransition_cocycle : ∀ (i j k : cover.index) (W : X.Opens)
      (hWi : W ≤ cover.opens i) (hWj : W ≤ cover.opens j) (hWk : W ≤ cover.opens k),
      canonicalTransition i j W hWi hWj ≪≫ canonicalTransition j k W hWj hWk =
        canonicalTransition i k W hWi hWk) :
    ExceptionalInverseImageSetup f cover :=
  { exceptionalPullback
    exceptionalPullbackAdjunction
    canonicalTransition
    canonicalTransition_self
    canonicalTransition_cocycle }

/-- The canonical transition on the pairwise intersection of two members of the cover. -/
abbrev overlapTransition {S X : Scheme.{u}} {f : X ⟶ S}
    {cover : FiniteSeparatedOpenCover f} (duality : ExceptionalInverseImageSetup f cover)
    (i j : cover.index) :
    duality.exceptionalPullback i ⋙ RingedSpace.OpenSubspace.Restriction.derivedBetween
        X.toRingedSpace (inf_le_left : cover.opens i ⊓ cover.opens j ≤ cover.opens i) ≅
      duality.exceptionalPullback j ⋙ RingedSpace.OpenSubspace.Restriction.derivedBetween
        X.toRingedSpace (inf_le_right : cover.opens i ⊓ cover.opens j ≤ cover.opens j) :=
  duality.canonicalTransition i j (cover.opens i ⊓ cover.opens j) inf_le_left inf_le_right

/-- The pairwise overlap transition is the canonical transition specialized to the
intersection. -/
theorem overlapTransition_eq_canonicalTransition {S X : Scheme.{u}} {f : X ⟶ S}
    {cover : FiniteSeparatedOpenCover f} (duality : ExceptionalInverseImageSetup f cover)
    (i j : cover.index) :
    duality.overlapTransition i j =
      duality.canonicalTransition i j (cover.opens i ⊓ cover.opens j) inf_le_left inf_le_right :=
  sorry

end ExceptionalInverseImageSetup

namespace NormalizedDualizingComplexOnCover

/-- Restrict a local normalization isomorphism further to a smaller open, using the canonical
comparison between iterated and direct derived restriction. -/
noncomputable def restrictNormalizationIso {X : Scheme.{u}}
    (complex : RingedSpace.ModuleDerived X.toRingedSpace) {U W : X.Opens} (hWU : W ≤ U)
    {L : RingedSpace.moduleDerivedOnOpen X.toRingedSpace U}
    (e : (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj complex ≅ L) :
    (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace W).obj complex ≅
      (RingedSpace.OpenSubspace.Restriction.derivedBetween X.toRingedSpace hWU).obj L :=
  ((RingedSpace.OpenSubspace.Restriction.derivedCompIso X.toRingedSpace hWU).app complex).symm ≪≫
    (RingedSpace.OpenSubspace.Restriction.derivedBetween X.toRingedSpace hWU).mapIso e

/-- Restricted local normalization is given by the iterated/direct restriction comparison
followed by restriction of the original normalization. -/
theorem restrictNormalizationIso_def {X : Scheme.{u}}
    (complex : RingedSpace.ModuleDerived X.toRingedSpace) {U W : X.Opens} (hWU : W ≤ U)
    {L : RingedSpace.moduleDerivedOnOpen X.toRingedSpace U}
    (e : (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj complex ≅ L) :
    restrictNormalizationIso complex hWU e =
      ((RingedSpace.OpenSubspace.Restriction.derivedCompIso X.toRingedSpace hWU).app complex).symm ≪≫
        (RingedSpace.OpenSubspace.Restriction.derivedBetween X.toRingedSpace hWU).mapIso e :=
  sorry

end NormalizedDualizingComplexOnCover

/-- The output of the finite-cover construction: a complex on `X` together with local
normalizations relative to `ωS` whose induced maps on pairwise intersections are the canonical
exceptional-pullback transitions. -/
structure NormalizedDualizingComplexOnCover {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (cover : FiniteSeparatedOpenCover f) (duality : ExceptionalInverseImageSetup f cover) where
  /-- The global complex obtained from the finite-cover gluing construction. -/
  complex : RingedSpace.ModuleDerived X.toRingedSpace
  /-- The normalization isomorphism on each member of the chosen cover. -/
  normalizationIso (i : cover.index) :
    (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace (cover.opens i)).obj complex ≅
      (duality.exceptionalPullback i).obj ωS
  /-- On every pairwise intersection, the local normalizations induce the canonical transition. -/
  overlapCompatibility (i j : cover.index) :
    (NormalizedDualizingComplexOnCover.restrictNormalizationIso complex
        (inf_le_left : cover.opens i ⊓ cover.opens j ≤ cover.opens i)
        (normalizationIso i)).symm ≪≫
      NormalizedDualizingComplexOnCover.restrictNormalizationIso complex
        (inf_le_right : cover.opens i ⊓ cover.opens j ≤ cover.opens j)
        (normalizationIso j) =
      (duality.overlapTransition i j).app ωS

namespace NormalizedDualizingComplexOnCover

/-- Construct the output of the finite-cover gluing construction from its global complex,
coverwise normalization isomorphisms, and their canonical overlap compatibility. -/
def ofLocalNormalizations {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (cover : FiniteSeparatedOpenCover f) (duality : ExceptionalInverseImageSetup f cover)
    (complex : RingedSpace.ModuleDerived X.toRingedSpace)
    (normalizationIso : ∀ i : cover.index,
      (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace (cover.opens i)).obj complex ≅
        (duality.exceptionalPullback i).obj ωS)
    (overlapCompatibility : ∀ i j : cover.index,
      (restrictNormalizationIso complex
          (inf_le_left : cover.opens i ⊓ cover.opens j ≤ cover.opens i)
          (normalizationIso i)).symm ≪≫
        restrictNormalizationIso complex
          (inf_le_right : cover.opens i ⊓ cover.opens j ≤ cover.opens j)
          (normalizationIso j) =
        (duality.overlapTransition i j).app ωS) :
    NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality :=
  { complex
    normalizationIso
    overlapCompatibility }

/-- The complex produced by the finite separated-cover construction is dualizing on `X`. -/
theorem complex_isDualizing {S X : Scheme.{u}} [IsNoetherian S]
    {f : X ⟶ S} [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    {HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex HS}
    {cover : FiniteSeparatedOpenCover f} {duality : ExceptionalInverseImageSetup f cover}
    (K : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality) :
    K.complex.IsDualizingComplex HX := sorry

end NormalizedDualizingComplexOnCover

end AlgebraicGeometry.Scheme.Hom
