module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Characterizations of finite-type points of algebraic spaces

A point of an algebraic space is of finite type if and only if it is the image
of a locally-of-finite-type morphism from a singleton algebraic space, and if
and only if it is the image of a monomorphism that is locally of finite type
from an algebraic space admitting a surjective étale morphism from the
spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

/-- There exists an algebraic space `Z` over `S` whose space of points is a
singleton, together with a locally-of-finite-type morphism `f : Z ⟶ X` whose
image on points is `{x}`. -/
def existsSingletonLocallyOfFiniteType : Prop :=
  ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X),
    Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧ LocallyOfFiniteType f ∧
      Set.range (Points.map f) = {x}

/-- `existsSingletonLocallyOfFiniteType x` means some locally-of-finite-type
morphism from a singleton algebraic space has image `{x}` on points. -/
theorem existsSingletonLocallyOfFiniteType_iff :
    existsSingletonLocallyOfFiniteType x ↔
      ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X),
        Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧ LocallyOfFiniteType f ∧
          Set.range (Points.map f) = {x} :=
  sorry

/-- `existsSingletonLocallyOfFiniteType x` is equivalent to the existence of a
locally-of-finite-type morphism from an algebraic space whose underlying point
set is a singleton `{z}` with image `{x}`. -/
theorem existsSingletonLocallyOfFiniteType_iff_univ :
    existsSingletonLocallyOfFiniteType x ↔
      ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X) (z : Points Z),
        (Set.univ : Set (Points Z)) = {z} ∧ LocallyOfFiniteType f ∧
          Set.range (Points.map f) = {x} :=
  sorry

namespace existsSingletonLocallyOfFiniteType

/-- A locally-of-finite-type morphism from a singleton algebraic space with
image `{x}` witnesses `existsSingletonLocallyOfFiniteType x`. -/
theorem of {Z : AlgebraicSpace S} {f : Z ⟶ X} [Nonempty (Points Z)]
    [Subsingleton (Points Z)] [LocallyOfFiniteType f]
    (hx : Set.range (Points.map f) = {x}) :
    existsSingletonLocallyOfFiniteType x :=
  sorry

/-- `existsSingletonLocallyOfFiniteType x` supplies a singleton algebraic space
over `S` and a locally-of-finite-type morphism to `X` with image `{x}`. -/
theorem spec (h : existsSingletonLocallyOfFiniteType x) :
    ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X),
      Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧ LocallyOfFiniteType f ∧
        Set.range (Points.map f) = {x} :=
  sorry

end existsSingletonLocallyOfFiniteType

/-- There exists an algebraic space `Z` over `S`, a monomorphism `f : Z ⟶ X`
that is locally of finite type, and a field-valued point of `Z` whose morphism
is surjective and étale, such that `f` sends that point to `x`. -/
def existsEtaleFieldMono : Prop :=
  ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X) (p : FieldValuedPoint Z),
    Surjective p.hom ∧ Etale p.hom ∧ LocallyOfFiniteType f ∧ Mono f ∧
      Points.map f (Points.mk p) = x

/-- `existsEtaleFieldMono x` means some monomorphism `f : Z ⟶ X` that is
locally of finite type receives a surjective étale field-valued point mapping
to `x`. -/
theorem existsEtaleFieldMono_iff :
    existsEtaleFieldMono x ↔
      ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X) (p : FieldValuedPoint Z),
        Surjective p.hom ∧ Etale p.hom ∧ LocallyOfFiniteType f ∧ Mono f ∧
          Points.map f (Points.mk p) = x :=
  sorry

/-- `existsEtaleFieldMono x` expands the field-valued point to a morphism
`Spec(k) ⟶ Z` over `S` from the spectrum of a field. -/
theorem existsEtaleFieldMono_iff_specField :
    existsEtaleFieldMono x ↔
      ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X) (k : Type u) (hk : Field k)
        (σ : Spec (.of k) ⟶ S) (zHom : ofOver (Over.mk σ) ⟶ Z),
        Surjective zHom ∧ Etale zHom ∧ LocallyOfFiniteType f ∧ Mono f ∧
          Points.map f (Points.mk (FieldValuedPoint.of k σ zHom)) = x :=
  sorry

namespace existsEtaleFieldMono

/-- A monomorphism that is locally of finite type, together with a surjective
étale field-valued point sent to `x`, witnesses `existsEtaleFieldMono x`. -/
theorem of {Z : AlgebraicSpace S} {f : Z ⟶ X} {p : FieldValuedPoint Z}
    [Surjective p.hom] [Etale p.hom] [LocallyOfFiniteType f] [Mono f]
    (hx : Points.map f (Points.mk p) = x) : existsEtaleFieldMono x :=
  sorry

/-- A surjective étale morphism `Spec(k) ⟶ Z` from a field spectrum, together
with a monomorphism `f : Z ⟶ X` that is locally of finite type sending that
point to `x`, witnesses `existsEtaleFieldMono x`. -/
theorem of_specField {Z : AlgebraicSpace S} {f : Z ⟶ X} (k : Type u) [Field k]
    (σ : Spec (.of k) ⟶ S) (zHom : ofOver (Over.mk σ) ⟶ Z) [Surjective zHom]
    [Etale zHom] [LocallyOfFiniteType f] [Mono f]
    (hx : Points.map f (Points.mk (FieldValuedPoint.of k σ zHom)) = x) :
    existsEtaleFieldMono x :=
  sorry

/-- `existsEtaleFieldMono x` supplies a monomorphism that is locally of finite
type and a surjective étale field-valued point of the source mapping to `x`. -/
theorem spec (h : existsEtaleFieldMono x) :
    ∃ (Z : AlgebraicSpace S) (f : Z ⟶ X) (p : FieldValuedPoint Z),
      Surjective p.hom ∧ Etale p.hom ∧ LocallyOfFiniteType f ∧ Mono f ∧
        Points.map f (Points.mk p) = x :=
  sorry

end existsEtaleFieldMono

/-- For every point of an algebraic space over a scheme, being of finite type
is equivalent to either singleton-source or étale-field-monomorphism
characterization. -/
theorem isFiniteTypePoint_tfae :
    List.TFAE
      [IsFiniteTypePoint x, existsSingletonLocallyOfFiniteType x,
        existsEtaleFieldMono x] :=
  sorry

/-- A point of an algebraic space is of finite type if and only if it is the
image of a locally-of-finite-type morphism from a singleton algebraic space. -/
theorem isFiniteTypePoint_iff_existsSingletonLocallyOfFiniteType :
    IsFiniteTypePoint x ↔ existsSingletonLocallyOfFiniteType x :=
  sorry

/-- A point of an algebraic space is of finite type if and only if it is the
image of a monomorphism that is locally of finite type from an algebraic space
admitting a surjective étale field-valued point. -/
theorem isFiniteTypePoint_iff_existsEtaleFieldMono :
    IsFiniteTypePoint x ↔ existsEtaleFieldMono x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
