module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Truncation
public import ReasLib.CategoryTheory.Filtration.Complex.Computation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of the canonical truncation filtration

The canonical `τ≤` filtration is functorial in a cochain complex.  This leaf owns the
degreewise filtered map, the induced filtered-complex map, and the fixed-stage and
fixed-graded-piece functors.  The comparison with the canonical upper truncation is
recorded as a natural isomorphism, so applications can use the filtration without
reconstructing its degreewise factorization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open FilteredObject

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.TruncationFiltration

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A cochain map preserves the canonical truncation filtration in every degree. -/
theorem mapComponent_preserves {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (p n : ℤ) :
    (truncationFiltrationSubobject L p n).Factors
      ((truncationFiltrationSubobject K p n).arrow ≫ f.f n) := sorry

/-- The filtered-object map in degree `n` induced by a cochain map. -/
@[stacks 015X "degreewise map of canonical truncation filtrations"]
def mapComponent {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (K.truncationFiltration).X n ⟶ (L.truncationFiltration).X n where
  hom := f.f n
  preserves := fun p ↦ mapComponent_preserves f p n

/-- Forgetting the filtration on a degree component recovers the original cochain-map
component. -/
@[simp]
theorem mapComponent_hom {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (mapComponent f n).hom = f.f n := sorry

/-- The filtered degree components induced by a cochain map commute with the differentials. -/
theorem mapComponent_comm {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    mapComponent f i ≫ (L.truncationFiltration).d i j =
      (K.truncationFiltration).d i j ≫ mapComponent f j := sorry

/-- A cochain map induces the canonical map of truncation-filtered complexes. -/
@[stacks 015X "map of canonical truncation filtrations"]
def map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    K.truncationFiltration ⟶ L.truncationFiltration where
  f := mapComponent f
  comm' := mapComponent_comm f

/-- The degree component of the map of truncation filtrations is the canonical filtered-object
map. -/
@[simp, stacks 015X]
theorem map_f {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (map f).f n = mapComponent f n := sorry

/-- Forgetting a map of truncation filtrations recovers the original cochain map. -/
@[simp, stacks 015X]
theorem underlyingMap {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (K.truncationFiltration).underlyingMap (map f) = f := sorry

/-- The truncation-filtration map of an identity is an identity. -/
@[simp]
theorem map_id (K : CochainComplex A ℤ) :
    map (𝟙 K) = 𝟙 K.truncationFiltration := sorry

/-- Truncation-filtration maps preserve composition. -/
@[simp]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

variable (A) in
/-- Equipping a cochain complex with its canonical truncation filtration is functorial. -/
@[stacks 015X "canonical truncation filtration functor"]
def functor : CochainComplex A ℤ ⥤ FilteredComplex A where
  obj := truncationFiltration
  map := map
  map_id := map_id
  map_comp := map_comp

/-- Evaluating the truncation-filtration functor equips a complex with its canonical filtration. -/
@[simp, stacks 015X]
theorem functor_obj (K : CochainComplex A ℤ) :
    (functor A).obj K = K.truncationFiltration := sorry

/-- The map of the truncation-filtration functor is the canonical filtered map. -/
@[simp, stacks 015X]
theorem functor_map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor A).map f = map f := sorry

namespace Stage

variable (A) in
/-- The functor selecting a fixed stage of the canonical truncation filtration. -/
@[stacks 015X "fixed stage of the canonical truncation filtration"]
abbrev functor (p : ℤ) :
    CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  TruncationFiltration.functor A ⋙ FilteredComplex.Stage.functor p

/-- The map on the `p`-th truncation-filtration stage induced by a cochain map. -/
@[stacks 015X]
abbrev map {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    (K.truncationFiltration).stage p ⟶ (L.truncationFiltration).stage p :=
  (functor (A := A) p).map f

/-- Evaluating the fixed-stage functor on an object is the corresponding filtration stage. -/
@[simp]
theorem functor_obj (K : CochainComplex A ℤ) (p : ℤ) :
    (functor (A := A) p).obj K = (K.truncationFiltration).stage p := sorry

/-- The fixed-stage map is evaluated degreewise by the filtered-object stage map. -/
@[simp, stacks 015X]
theorem map_f {K L : CochainComplex A ℤ} (f : K ⟶ L) (p n : ℤ) :
    (map f p).f n = (mapComponent f n).stageMap p := sorry

/-- The map on a fixed truncation-filtration stage preserves identities. -/
@[simp]
theorem map_id (K : CochainComplex A ℤ) (p : ℤ) :
    map (𝟙 K) p = 𝟙 ((K.truncationFiltration).stage p) := sorry

/-- Maps on a fixed truncation-filtration stage preserve composition. -/
@[simp]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    map (f ≫ g) p = map f p ≫ map g p := sorry

/-- A fixed truncation-filtration stage map commutes with its inclusion into the original complex. -/
@[reassoc, stacks 015X]
theorem map_comp_inclusion {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    map f p ≫ (L.truncationFiltration).stageInclusion p =
      (K.truncationFiltration).stageInclusion p ≫ f := sorry

/-- The canonical stage comparison is natural after identifying stages with `τ≤`. -/
@[reassoc, stacks 015X "naturality of the canonical truncation stage comparison"]
theorem iso_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    map f p ≫ (TruncationFiltration.stageIso L p).hom =
      (TruncationFiltration.stageIso K p).hom ≫
        _root_.CochainComplex.truncLEMap f (-p) := sorry

variable (A) in
/-- The fixed-stage functor is naturally isomorphic to the canonical `τ≤ -p` functor. -/
@[stacks 015X "stage comparison with canonical upper truncation"]
noncomputable def iso (p : ℤ) :
    functor A p ≅ (embeddingUpIntLE (-p)).truncLEFunctor A :=
  NatIso.ofComponents (fun K ↦ TruncationFiltration.stageIso K p)
    (fun f ↦ iso_naturality f p)

/-- The forward component of the fixed-stage comparison is `stageIso`. -/
@[simp, stacks 015X]
theorem iso_hom_app (K : CochainComplex A ℤ) (p : ℤ) :
    (iso A p).hom.app K = (TruncationFiltration.stageIso K p).hom := sorry

/-- The inverse component of the fixed-stage comparison is `stageIso.inv`. -/
@[simp, stacks 015X]
theorem iso_inv_app (K : CochainComplex A ℤ) (p : ℤ) :
    (iso A p).inv.app K = (TruncationFiltration.stageIso K p).inv := sorry

end Stage

namespace GradedPiece

variable (A) in
/-- The functor selecting a fixed associated-graded piece of the canonical truncation filtration. -/
@[stacks 015X "fixed graded piece of the canonical truncation filtration"]
noncomputable abbrev functor (p : ℤ) :
    CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  TruncationFiltration.functor A ⋙ FilteredComplex.gradedPieceFunctor p

/-- The map on a fixed graded piece induced by a cochain map. -/
@[stacks 015X]
noncomputable abbrev map {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    (K.truncationFiltration).gradedPiece p ⟶ (L.truncationFiltration).gradedPiece p :=
  (functor (A := A) p).map f

/-- Evaluating the fixed graded-piece functor gives the corresponding graded piece. -/
@[simp]
theorem functor_obj (K : CochainComplex A ℤ) (p : ℤ) :
    (functor (A := A) p).obj K = (K.truncationFiltration).gradedPiece p := sorry

/-- The fixed graded-piece map is evaluated degreewise by the filtered-object graded-piece map. -/
@[simp, stacks 015X]
theorem map_f {K L : CochainComplex A ℤ} (f : K ⟶ L) (p n : ℤ) :
    (map f p).f n = (mapComponent f n).gradedPieceMap p := sorry

/-- The map on a fixed graded piece preserves identities. -/
@[simp]
theorem map_id (K : CochainComplex A ℤ) (p : ℤ) :
    map (𝟙 K) p = 𝟙 ((K.truncationFiltration).gradedPiece p) := sorry

/-- Maps on a fixed graded piece preserve composition. -/
@[simp]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    map (f ≫ g) p = map f p ≫ map g p := sorry

end GradedPiece

namespace AssociatedGraded

variable (A) in
/-- The associated-graded functor of the canonical truncation filtration. -/
@[stacks 015X "associated graded of the canonical truncation filtration"]
noncomputable abbrev functor :
    CochainComplex A ℤ ⥤ CochainComplex (GradedObject ℤ A) ℤ :=
  TruncationFiltration.functor A ⋙ FilteredComplex.associatedGradedFunctor

/-- The associated-graded map induced by a cochain map. -/
@[stacks 015X]
noncomputable abbrev map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (K.truncationFiltration).associatedGraded ⟶
      (L.truncationFiltration).associatedGraded :=
  (functor (A := A)).map f

/-- Evaluating the associated-graded functor gives the associated-graded complex. -/
@[simp]
theorem functor_obj (K : CochainComplex A ℤ) :
    (functor (A := A)).obj K = (K.truncationFiltration).associatedGraded := sorry

/-- The associated-graded map is evaluated degreewise by the filtered-object associated-graded
map. -/
@[simp, stacks 015X]
theorem map_f {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (map f).f n = (mapComponent f n).associatedGradedMap := sorry

/-- The associated-graded map of an identity is an identity. -/
@[simp]
theorem map_id (K : CochainComplex A ℤ) :
    map (𝟙 K) = 𝟙 ((K.truncationFiltration).associatedGraded) := sorry

/-- Associated-graded maps preserve composition. -/
@[simp]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

end AssociatedGraded

end CategoryTheory.CochainComplex.TruncationFiltration
