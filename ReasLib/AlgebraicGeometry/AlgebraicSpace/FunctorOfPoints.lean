module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Algebraic spaces via functors of points

This module records the functor-of-points characterization of algebraic spaces over a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- An algebraic space over `S` is represented by a functor of points on schemes over `S` that is
an fppf sheaf with representable diagonal and a representable étale locally-surjective atlas. -/
structure Obj (S : Scheme.{u}) where
  /-- The functor of points on schemes over the base. -/
  functorOfPoints : (Over S)ᵒᵖ ⥤ Type u
  /-- The functor of points satisfies fppf descent. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) functorOfPoints
  /-- The diagonal of the functor of points is representable by schemes. -/
  representableDiagonal :
    yoneda.relativelyRepresentable (Limits.diag functorOfPoints)
  /-- There is a representable étale atlas that is locally surjective. -/
  atlas : ∃ (U : Over S) (p : yoneda.obj U ⟶ functorOfPoints),
    MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p

/-- Construct an algebraic-space object from its functor of points and defining conditions. -/
def Obj.ofFunctor {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (representableDiagonal : yoneda.relativelyRepresentable (Limits.diag F))
    (atlas : ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) :
    Obj S where
  functorOfPoints := F
  isSheaf := isSheaf
  representableDiagonal := representableDiagonal
  atlas := atlas

/-- The category whose objects are algebraic spaces over `S` and whose morphisms are natural
transformations of their functors of points. -/
def category (S : Scheme.{u}) : CategoryTheory.Cat.{u + 1, u + 1} :=
  ⟨Obj S, {
    Hom := fun F F' ↦ F.functorOfPoints ⟶ F'.functorOfPoints
    id := fun F ↦ 𝟙 F.functorOfPoints
    comp := fun f g ↦ NatTrans.vcomp f g
    id_comp := fun _ ↦ rfl
    comp_id := fun _ ↦ rfl
    assoc := fun _ _ _ ↦ rfl
  }⟩

end AlgebraicSpace

/-- The type-valued carrier of the category of algebraic spaces over `S`. -/
abbrev AlgebraicSpace (S : Scheme.{u}) : Type (u + 1) := AlgebraicSpace.category S

namespace AlgebraicSpace

/-- Construct an algebraic space from a functor of points satisfying fppf descent, representable
diagonal, and the existence of a representable étale locally-surjective atlas. -/
def ofFunctor {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (representableDiagonal : yoneda.relativelyRepresentable (Limits.diag F))
    (atlas : ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) :
    AlgebraicSpace S := Obj.ofFunctor F isSheaf representableDiagonal atlas

/-- The functor of points of an algebraic space over `S`. -/
abbrev functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) : (Over S)ᵒᵖ ⥤ Type u :=
  Obj.functorOfPoints X

/-- The fppf-sheaf condition of an algebraic space over `S`. -/
abbrev isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Obj.functorOfPoints X) :=
  Obj.isSheaf X

/-- The representability of the diagonal of an algebraic space over `S`. -/
abbrev representableDiagonal {S : Scheme.{u}} (X : AlgebraicSpace S) :
    yoneda.relativelyRepresentable (Limits.diag (Obj.functorOfPoints X)) :=
  Obj.representableDiagonal X

/-- The representable étale locally-surjective atlas condition of an algebraic space over `S`. -/
abbrev atlas {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ Obj.functorOfPoints X),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  Obj.atlas X

/-- The functor of points of `ofFunctor F isSheaf representableDiagonal atlas` is `F`. -/
@[simp]
theorem ofFunctor_functorOfPoints {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (representableDiagonal : yoneda.relativelyRepresentable (Limits.diag F))
    (atlas : ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) :
    (ofFunctor F isSheaf representableDiagonal atlas).functorOfPoints = F := sorry

/-- The algebraic space constructed by `ofFunctor` satisfies the fppf sheaf, representable
diagonal, and representable étale locally-surjective atlas conditions. -/
theorem ofFunctor_spec {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    (isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (representableDiagonal : yoneda.relativelyRepresentable (Limits.diag F))
    (atlas : ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) :
    let X := ofFunctor F isSheaf representableDiagonal atlas
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The representable functor `yoneda.obj T` is an fppf sheaf on schemes over `S`. -/
theorem ofOver_isSheaf {S : Scheme.{u}} (T : Over S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj T) := sorry

/-- The diagonal of the representable functor `yoneda.obj T` is representable by schemes over `S`. -/
theorem ofOver_representableDiagonal {S : Scheme.{u}} (T : Over S) :
    yoneda.relativelyRepresentable (Limits.diag (yoneda.obj T)) := sorry

/-- The identity transformation of `yoneda.obj T` is representable and étale. -/
theorem ofOver_id_presheaf_etale {S : Scheme.{u}} (T : Over S) :
    (MorphismProperty.over (@Etale)).presheaf (𝟙 (yoneda.obj T)) := sorry

/-- The identity transformation of `yoneda.obj T` is étale-locally surjective. -/
theorem ofOver_id_locallySurjective {S : Scheme.{u}} (T : Over S) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (𝟙 (yoneda.obj T)) := sorry

/-- Construct the algebraic space over `S` represented by a scheme `T` over `S`. -/
def ofOver {S : Scheme.{u}} (T : Over S) : AlgebraicSpace S :=
  ofFunctor (yoneda.obj T) (ofOver_isSheaf T) (ofOver_representableDiagonal T)
    ⟨T, 𝟙 (yoneda.obj T), ofOver_id_presheaf_etale T, ofOver_id_locallySurjective T⟩

/-- The functor of points of the algebraic space represented by `T` is `yoneda.obj T`. -/
@[simp]
theorem ofOver_functorOfPoints {S : Scheme.{u}} (T : Over S) :
    (ofOver T).functorOfPoints = yoneda.obj T := sorry

/-- The algebraic space represented by `T` has the fppf sheaf and representable diagonal
properties, together with its identity étale locally-surjective atlas. -/
theorem ofOver_spec {S : Scheme.{u}} (T : Over S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (ofOver T).functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag (ofOver T).functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ (ofOver T).functorOfPoints),
          (MorphismProperty.over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- A functor of points on schemes over `S` is an algebraic space when it is an fppf sheaf
with representable diagonal and a representable étale locally-surjective atlas. -/
class IsAlgebraicSpace {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- The functor of points satisfies fppf descent. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F
  /-- The diagonal of the functor of points is representable by schemes. -/
  representableDiagonal : yoneda.relativelyRepresentable (Limits.diag F)
  /-- There is a representable étale atlas that is locally surjective. -/
  atlas : ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
    MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p

/-- The functor of points of a bundled algebraic space is an algebraic space. -/
theorem instIsAlgebraicSpace_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAlgebraicSpace X.functorOfPoints :=
  ⟨X.isSheaf, X.representableDiagonal, X.atlas⟩

/-- The representable presheaf of a scheme over `S` is an algebraic space with its identity
étale locally-surjective atlas. -/
instance instIsAlgebraicSpaceYoneda {S : Scheme.{u}} (T : Over S) :
    IsAlgebraicSpace (yoneda.obj T) where
  isSheaf := ofOver_isSheaf T
  representableDiagonal := ofOver_representableDiagonal T
  atlas := ⟨T, 𝟙 (yoneda.obj T), ofOver_id_presheaf_etale T, ofOver_id_locallySurjective T⟩

/-- Construct a bundled algebraic space from a functor of points satisfying the
algebraic-space recognition conditions. -/
def ofIsAlgebraicSpace {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) [IsAlgebraicSpace F] :
    AlgebraicSpace S :=
  ofFunctor F IsAlgebraicSpace.isSheaf IsAlgebraicSpace.representableDiagonal
    IsAlgebraicSpace.atlas

/-- The functor of points of `ofIsAlgebraicSpace F` is `F`. -/
@[simp]
theorem ofIsAlgebraicSpace_functorOfPoints {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
    [IsAlgebraicSpace F] :
    (ofIsAlgebraicSpace F).functorOfPoints = F := sorry

/-- A functor of points is an algebraic space if and only if it is an fppf sheaf with
representable diagonal and a representable étale locally-surjective atlas. -/
theorem isAlgebraicSpace_iff {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    IsAlgebraicSpace F ↔
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F ∧
        yoneda.relativelyRepresentable (Limits.diag F) ∧
          ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
            MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
              Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

end AlgebraicSpace
end AlgebraicGeometry
