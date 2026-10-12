/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Algebraic spaces over Spec ℤ

An algebraic space `X` over `S` may be viewed as an algebraic space over `Spec ℤ` by recording,
for each test scheme `T`, a structure morphism `T ⟶ S` together with a `T`-point of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A `T`-point of `X` viewed over `Spec ℤ`: a structure morphism `T ⟶ S` together with a
`T`-point of `X` over `S`. -/
structure ToSpecZPoint {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Scheme.{u}) where
  /-- The structure morphism of the test scheme over `S`. -/
  structureHom : T ⟶ S
  /-- The `T`-point of `X` over `S` along `structureHom`. -/
  point : X.functorOfPoints.obj (op (Over.mk structureHom))

namespace ToSpecZPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Scheme.{u}}

/-- Construct a `Spec ℤ`-point of `X` from a structure morphism and a `T`-point of `X`. -/
def of (structureHom : T ⟶ S) (point : X.functorOfPoints.obj (op (Over.mk structureHom))) :
    ToSpecZPoint X T where
  structureHom := structureHom
  point := point

/-- The structure morphism of `ToSpecZPoint.of structureHom point` is `structureHom`. -/
@[simp]
theorem of_structureHom (structureHom : T ⟶ S)
    (point : X.functorOfPoints.obj (op (Over.mk structureHom))) :
    (of structureHom point).structureHom = structureHom :=
  sorry

/-- The point of `ToSpecZPoint.of structureHom point` is `point`. -/
@[simp]
theorem of_point (structureHom : T ⟶ S)
    (point : X.functorOfPoints.obj (op (Over.mk structureHom))) :
    (of structureHom point).point = point :=
  sorry

/-- Two `Spec ℤ`-points of `X` agree if their structure morphisms and points agree. -/
theorem ext {p q : ToSpecZPoint X T} (h_structureHom : p.structureHom = q.structureHom)
    (h_point : HEq p.point q.point) : p = q :=
  sorry

/-- The morphism in `Over S` induced by restricting the structure morphism along `f`. -/
def restrictHom (p : ToSpecZPoint X T) {T' : Scheme.{u}} (f : T' ⟶ T) :
    Over.mk (f ≫ p.structureHom) ⟶ Over.mk p.structureHom :=
  Over.homMk f

/-- `restrictHom p f` is the over-morphism with underlying map `f`. -/
theorem restrictHom_left (p : ToSpecZPoint X T) {T' : Scheme.{u}} (f : T' ⟶ T) :
    (p.restrictHom f).left = f :=
  sorry

/-- Restrict a `Spec ℤ`-point of `X` along a morphism of test schemes. -/
def restrict (p : ToSpecZPoint X T) {T' : Scheme.{u}} (f : T' ⟶ T) : ToSpecZPoint X T' where
  structureHom := f ≫ p.structureHom
  point := X.functorOfPoints.map (p.restrictHom f).op p.point

/-- Restriction postcomposes the structure morphism. -/
@[simp]
theorem restrict_structureHom (p : ToSpecZPoint X T) {T' : Scheme.{u}} (f : T' ⟶ T) :
    (p.restrict f).structureHom = f ≫ p.structureHom :=
  sorry

/-- Restriction acts on the point of `X` by the opposite of `restrictHom`. -/
@[simp]
theorem restrict_point (p : ToSpecZPoint X T) {T' : Scheme.{u}} (f : T' ⟶ T) :
    (p.restrict f).point = X.functorOfPoints.map (p.restrictHom f).op p.point :=
  sorry

end ToSpecZPoint

/-- The functor of points of `X` viewed as an algebraic space over `Spec ℤ`. -/
def toSpecZFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Over (Spec (.of (ULift.{u} ℤ))))ᵒᵖ ⥤ Type u where
  obj T := ToSpecZPoint X T.unop.left
  map f := TypeCat.ofHom fun p ↦ p.restrict f.unop.left
  map_id := sorry
  map_comp := sorry

/-- Evaluating `toSpecZFunctor X` at `T` gives the type of `Spec ℤ`-points of `X` on `T.left`. -/
theorem toSpecZFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Over (Spec (.of (ULift.{u} ℤ)))) :
    (toSpecZFunctor X).obj (op T) = ToSpecZPoint X T.left :=
  sorry

/-- `toSpecZFunctor X` acts on a morphism by restriction of `Spec ℤ`-points. -/
theorem toSpecZFunctor_map {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T T' : (Over (Spec (.of (ULift.{u} ℤ))))ᵒᵖ} (f : T ⟶ T') (p : ToSpecZPoint X T.unop.left) :
    (toSpecZFunctor X).map f p = p.restrict f.unop.left :=
  sorry

/-- The algebraic space over `Spec ℤ` obtained by viewing `X` as an algebraic space over `ℤ`. -/
def toSpecZ {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace (Spec (.of (ULift.{u} ℤ))) :=
  ofFunctor (toSpecZFunctor X) sorry sorry sorry

/-- The functor of points of `toSpecZ X` is `toSpecZFunctor X`. -/
@[simp]
theorem toSpecZ_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (toSpecZ X).functorOfPoints = toSpecZFunctor X :=
  sorry

/-- `toSpecZ X` is an fppf sheaf with representable diagonal and a representable étale
locally-surjective atlas. -/
theorem toSpecZ_spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of (ULift.{u} ℤ))))
        (toSpecZ X).functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag (toSpecZ X).functorOfPoints) ∧
        ∃ (U : Over (Spec (.of (ULift.{u} ℤ))))
          (p : yoneda.obj U ⟶ (toSpecZ X).functorOfPoints),
          (MorphismProperty.over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective
              (Scheme.etaleTopology.over (Spec (.of (ULift.{u} ℤ)))) p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
