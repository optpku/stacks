/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.DifferentialObject
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Homology.ShortComplex.Cycles

/-!
# Shifted Differential Objects

A shifted differential object for an autoequivalence `T` consists of a morphism `d : X ⟶ T X`
whose translate composes with `d` to zero.  The module supplies its canonical short complex,
homology, morphism category, and functorial homology API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

namespace ShiftedDifferentialObject

namespace Differential

/-- The morphism `T⁻¹ E ⟶ E` induced by `d : E ⟶ T(E)`. -/
@[stacks 0AMI "shifted previous differential"]
noncomputable abbrev previous (T : A ⥤ A) [Functor.IsEquivalence T]
    {E : A} (d : E ⟶ T.obj E) : T.inv.obj E ⟶ E :=
  T.inv.map d ≫ T.asEquivalence.unitInv.app E

/-- A map commuting with shifted differentials also commutes with the translated previous
 differential. -/
theorem naturality (T : A ⥤ A) [Functor.IsEquivalence T]
    {E₁ E₂ : A} {d₁ : E₁ ⟶ T.obj E₁} {d₂ : E₂ ⟶ T.obj E₂}
    (f : E₁ ⟶ E₂) (h : f ≫ d₂ = d₁ ≫ T.map f) :
    T.inv.map f ≫ previous T d₂ = previous T d₁ ≫ f := sorry

/-- The translated previous differential composes with `d` to zero. -/
@[stacks 0AMI "shifted differential zero composite"]
theorem comp (T : A ⥤ A) [Functor.IsEquivalence T]
    [Abelian A]
    {E : A} (d : E ⟶ T.obj E) (hd : d ≫ T.map d = 0) :
    previous T d ≫ d = 0 := sorry

/-- Mapping the translated previous differential through the equivalence collapses to the
original differential after the counit comparison. -/
theorem map (T : A ⥤ A) [Functor.IsEquivalence T]
    {E : A} (d : E ⟶ T.obj E) :
    T.map (previous T d) = T.asEquivalence.counit.app E ≫ d := sorry

/-- The short complex `T⁻¹E ⟶ E ⟶ TE` attached to a differential and an explicitly supplied
zero-composite witness. -/
@[stacks 0AMI "shifted differential short complex from zero composite"]
noncomputable abbrev shortComplexOfZero (T : A ⥤ A) [Functor.IsEquivalence T]
    [HasZeroMorphisms A]
    {E : A} (d : E ⟶ T.obj E) (hzero : previous T d ≫ d = 0) : ShortComplex A :=
  ShortComplex.mk
    (previous T d)
    d
    hzero

/-- The induced short complex `T⁻¹E ⟶ E ⟶ TE` attached to a square-zero shifted differential. -/
@[stacks 0AMI "shifted differential short complex"]
noncomputable abbrev shortComplex (T : A ⥤ A) [Functor.IsEquivalence T]
    [Abelian A]
    {E : A} (d : E ⟶ T.obj E) (hd : d ≫ T.map d = 0) : ShortComplex A :=
  shortComplexOfZero T d (comp T d hd)

end Differential

end ShiftedDifferentialObject

section Basic

variable [HasZeroMorphisms A]

/-- A page endowed with a shifted differential `d : E ⟶ T(E)` squaring to zero. -/
@[stacks 0AMI]
structure ShiftedDifferentialObject (T : A ⥤ A) [Functor.IsEquivalence T] where
  /-- The underlying object. -/
  obj : A
  /-- The differential from the object to its translate. -/
  d : obj ⟶ T.obj obj
  /-- Applying the translated differential after the differential gives zero. -/
  d_squared : d ≫ T.map d = 0

namespace ShiftedDifferentialObject

variable {T : A ⥤ A} [Functor.IsEquivalence T]

/-- Morphisms of shifted differential objects. -/
@[ext, stacks 0AMI "shifted differential-object morphism"]
structure Hom (X Y : ShiftedDifferentialObject T) where
  /-- The underlying morphism. -/
  hom : X.obj ⟶ Y.obj
  /-- Compatibility with the shifted differentials. -/
  comm : hom ≫ Y.d = X.d ≫ T.map hom

namespace Hom

/-- The identity underlying map commutes with the shifted differential. -/
theorem id_comm (X : ShiftedDifferentialObject T) :
    𝟙 X.obj ≫ X.d = X.d ≫ T.map (𝟙 X.obj) := sorry

/-- The identity morphism of a shifted differential object. -/
def id (X : ShiftedDifferentialObject T) : Hom X X where
  hom := 𝟙 X.obj
  comm := id_comm X

/-- Composites of underlying maps commute with the shifted differential. -/
theorem comp_comm {X Y Z : ShiftedDifferentialObject T} (f : Hom X Y) (g : Hom Y Z) :
    (f.hom ≫ g.hom) ≫ Z.d = X.d ≫ T.map (f.hom ≫ g.hom) := sorry

/-- The composite of two morphisms of shifted differential objects. -/
def comp {X Y Z : ShiftedDifferentialObject T} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  hom := f.hom ≫ g.hom
  comm := comp_comm f g

/-- Left identity for shifted-differential-object morphisms. -/
theorem id_comp {X Y : ShiftedDifferentialObject T} (f : Hom X Y) :
    comp (id X) f = f := sorry

/-- Right identity for shifted-differential-object morphisms. -/
theorem comp_id {X Y : ShiftedDifferentialObject T} (f : Hom X Y) :
    comp f (id Y) = f := sorry

/-- Associativity of shifted-differential-object morphism composition. -/
theorem assoc {W X Y Z : ShiftedDifferentialObject T}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Shifted differential objects for a fixed equivalence form a category. -/
instance : Category (ShiftedDifferentialObject T) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The underlying morphism of an identity shifted differential object morphism is the identity. -/
@[simp]
theorem id_hom (X : ShiftedDifferentialObject T) :
    (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := sorry

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem comp_hom {X Y Z : ShiftedDifferentialObject T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := sorry

/-- The functor forgetting a shifted differential and retaining its underlying object. -/
noncomputable def objFunctor : ShiftedDifferentialObject T ⥤ A where
  obj X := X.obj
  map f := f.hom
  map_id X := id_hom X
  map_comp f g := comp_hom f g

end ShiftedDifferentialObject

end Basic

section Homology

variable [Abelian A]

namespace ShiftedDifferentialObject

variable {T : A ⥤ A} [Functor.IsEquivalence T]

/-- The short complex `T⁻¹X ⟶ X ⟶ TX` attached to a shifted differential object. -/
@[stacks 0AMI "shifted-object short complex"]
noncomputable abbrev shortComplex (X : ShiftedDifferentialObject T) : ShortComplex A :=
  Differential.shortComplex T X.d X.d_squared

/-- The homology object `Ker(d) / Im(T⁻¹ d)` of a shifted differential object. -/
@[stacks 0AMI "shifted-object homology"]
noncomputable abbrev homology (X : ShiftedDifferentialObject T) : A :=
  X.shortComplex.homology

/-- The translated differential on the previous page still
 squares to zero after transporting back along the counit inverse. -/
theorem PreviousPage.d_squared (X : ShiftedDifferentialObject T) :
    (Differential.previous T X.d ≫ T.asEquivalence.counitInv.app X.obj) ≫
      T.map (Differential.previous T X.d ≫ T.asEquivalence.counitInv.app X.obj) = 0 := sorry

/-- The translated previous page `T⁻¹X`, whose differential is the translated previous
differential `T⁻¹ d`. -/
@[stacks 0AMI "shifted previous page"]
def previousPage (X : ShiftedDifferentialObject T) : ShiftedDifferentialObject T where
  obj := T.inv.obj X.obj
  d := Differential.previous T X.d ≫ T.asEquivalence.counitInv.app X.obj
  d_squared := PreviousPage.d_squared X

namespace PreviousPage

namespace Map

/-- The first differential in the mapped previous-page short
complex matches the original first differential through the counit comparisons. -/
theorem comm₁₂ (X : ShiftedDifferentialObject T) :
    (T.asEquivalence.counitIso.app (T.inv.obj X.obj)).hom ≫ X.shortComplex.f =
      (X.previousPage.shortComplex.map T).f ≫ (T.asEquivalence.counitIso.app X.obj).hom := sorry

/-- The second differential in the mapped previous-page short
complex matches the original differential through the counit comparisons. -/
theorem comm₂₃ (X : ShiftedDifferentialObject T) :
    (T.asEquivalence.counitIso.app X.obj).hom ≫ X.shortComplex.g =
      (X.previousPage.shortComplex.map T).g ≫
        (T.mapIso (T.asEquivalence.counitIso.app X.obj)).hom := sorry

end Map

open CategoryTheory.ShortComplex
/-- Mapping the previous-page short complex through `T`
recovers the original short complex via the counit comparisons. -/
noncomputable def shortComplexIso (X : ShiftedDifferentialObject T) :
    X.previousPage.shortComplex.map T ≅ X.shortComplex :=
    isoMk (T.asEquivalence.counitIso.app (T.inv.obj X.obj))
    (T.asEquivalence.counitIso.app X.obj)
    (T.mapIso (T.asEquivalence.counitIso.app X.obj))
    (Map.comm₁₂ X) (Map.comm₂₃ X)

/-- The homology of the previous page is canonically the translated homology `T⁻¹ H(X)`. -/
@[stacks 0AMI "shifted previous-page homology comparison"]
noncomputable def homologyIso (X : ShiftedDifferentialObject T) :
    X.previousPage.homology ≅ T.inv.obj X.homology :=
  T.asEquivalence.unitIso.app X.previousPage.homology ≪≫
    T.inv.mapIso ((X.previousPage.shortComplex.mapHomologyIso T).symm ≪≫
      ShortComplex.homologyMapIso (shortComplexIso X))

end PreviousPage

namespace Map

/-- The translated previous differentials commute with a morphism of shifted differential objects. -/
theorem comm₁₂ {X Y : ShiftedDifferentialObject T} (f : X ⟶ Y) :
    T.inv.map f.hom ≫ Y.shortComplex.f = X.shortComplex.f ≫ f.hom := sorry

/-- The outgoing shifted differentials commute with a morphism of shifted differential objects. -/
theorem comm₂₃ {X Y : ShiftedDifferentialObject T} (f : X ⟶ Y) :
    f.hom ≫ Y.shortComplex.g = X.shortComplex.g ≫ T.map f.hom := sorry

/-- The induced map of short complexes attached to a morphism of shifted differential objects. -/
noncomputable abbrev shortComplex {X Y : ShiftedDifferentialObject T} (φ : X ⟶ Y) :
    X.shortComplex ⟶ Y.shortComplex :=
  ShortComplex.homMk
    (T.inv.map φ.hom)
    φ.hom
    (T.map φ.hom)
    (comm₁₂ φ)
    (comm₂₃ φ)

end Map

/-- A morphism of shifted differential objects induces a morphism on homology. -/
noncomputable abbrev homologyMap {X Y : ShiftedDifferentialObject T} (φ : X ⟶ Y) :
  X.homology ⟶ Y.homology :=
  ShortComplex.homologyMap (Map.shortComplex φ)

namespace HomologyMap

/-- The map induced on shifted homology by an identity is the identity. -/
@[simp]
theorem id (X : ShiftedDifferentialObject T) :
    homologyMap (𝟙 X) = 𝟙 X.homology := sorry

/-- Shifted homology maps preserve composition. -/
@[simp]
theorem comp {X Y Z : ShiftedDifferentialObject T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homologyMap (f ≫ g) = homologyMap f ≫ homologyMap g := sorry

end HomologyMap

/-- The homology functor on shifted differential objects. -/
@[stacks 0AMI "shifted homology functor"]
noncomputable def homologyFunctor : ShiftedDifferentialObject T ⥤ A where
  obj X := X.homology
  map f := homologyMap f
  map_id X := HomologyMap.id X
  map_comp f g := HomologyMap.comp f g

end ShiftedDifferentialObject

end Homology

end CategoryTheory
